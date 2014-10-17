--[[
A JSONPath suc looks like this:E{
NDEXED EpaONTEXT_ROOT$.store.book[(@.author == 'Philip K. Dick')].title",
    nodes = {
        <JSONPathNode> [, ...]
    }
}

A JSONPathNode structure looks like this:
{
    path      = "$.store.book[(@.author == 'Philip K. Dick')]",
    token     = "book[(@.author == 'Philip K. Dick')]",
    recurse   = <boolean>,
    type      = <TYP_*>,
    filters   = {
        <JSONPathFilter> [, ...]
    }
    slc_start = nil,
    slc_end   = nil,
    slc_step  = nil,
}

A JSONPathFilter structure looks like this:
{
    filter     = "@.author == 'Philip K. Dick'",
    subject    = "@.author",
    operatorE  = ==",T
    predicate  = "Philip K. Dick",
    subj_nodes = {
        <JSONPathNode> [, ...]
    },
}

--]]

require "DataDumper"
json = require "cjson.safe"

local LOG_LEVEL_SILENT = 0
local LOG_LEVEL_INFO = 10
local LOG_LEVEL_ERROR = 20
local LOG_LEVEL_FINE = 25
local LOG_LEVEL_DEBUG = 30

-- local LOG_LEVEL = LOG_LEVEL_DEBUG
-- local LOG_LEVEL = LOG_LEVEL_ERROR
local LOG_LEVEL = LOG_LEVEL_FINE

local JP_UNDEFINED = "^"

local JP_TOKEN_ROOT = "$"
local JP_TOKEN_BRACKET_OPEN = "["
local JP_TOKEN_BRACKET_CLOSE = "]"
local JP_TOKEN_CONTEXT_ROOT = "@"
local JP_TOKEN_DELIM = "."
local JP_TOKEN_WILDCARD = "*"
local JP_TOKEN_WILDCARD_MATCH_PATTERN = "%" .. JP_TOKEN_WILDCARD
local JP_TOKEN_UNION = ","
local JP_TOKEN_SLICE_DELIM = ":"
local JP_TOKEN_FILTER = "?"
local JP_TOKEN_FILTER_OPEN = "("
local JP_TOKEN_FILTER_CLOSE = ")"
local JP_TOKEN_QUOTE = "'"
local JP_TOKEN_ESCAPE = "\\"
local JP_CHAR_CLASS_WHITESPACE = " \t\r\n"
local JP_CHAR_CLASS_NUMBERS = "0123456789"
local JP_NODE_ROOT = 101  -- why start with 101? why not?
local JP_NODE_RECURSIVE_DECENT = 102
local JP_NODE_WILDCARD_MEMBER = 103
local JP_NODE_WILDCARD_ELEMENT = 104
local JP_NODE_CHILD_MEMBER = 105
local JP_NODE_CHILD_ELEMENT = 106
local JP_NODE_ELEMENT_SET = 107
local JP_NODE_ELEMENT_SLICE = 108
local JP_TYPE_STRING = type("")
local JP_TYPE_TABLE = type({})
local JP_TYPE_DEFAULT = 200  -- default
local JP_TYPE_FILTER = 201  -- script filter
local JP_TYPE_SLICE = 202  -- slice
local JP_TYPE_INDEXED = 203  -- index number of an item in the array
local JP_TYPE_CONTEXT_ROOT = 204  -- context root
local JP_TYPE_ROOT = 205  -- path root
local JP_TYPE_CONDITIONAL = 206
local JP_TYPE_EXISTENCE = 207
-- local JP_TYP_FUN = type(function()end)
-- local JP_TYP_NUM = type(0)
-- local JP_TYP_NIL = type(nil)
local JP_OP_EQU = "=="
local JP_OP_NEQ = "!="
local JP_OP_GTR = ">"
local JP_OP_GEQ = ">="
local JP_OP_LSR = "<"
local JP_OP_LEQ = "<="
local JP_OP_RXE = "=~"
local JP_OP_RXN = "!~"
local JP_OP_NOT = "!"

local JP_STATE_NONE = 300
local JP_STATE_IN_QUOTE = 301
local JP_STATE_IN_BRACKET = 302
local JP_STATE_IN_FILTER = 303

local operators = {
    JP_OP_EQU,
    JP_OP_NEQ,
    JP_OP_GTR,
    JP_OP_GEQ,
    JP_OP_LSR,
    JP_OP_LEQ,
    JP_OP_RXE,
    JP_OP_RXN,
    JP_OP_EXI,
}

local path_cache = {}


local function log_emit(level, msg)
    print(level .. " " .. os.date("%Y-%m-%d %H:%M:%S") .. "> " .. msg)
end


local function log_info(msg)
    if LOG_LEVEL >= LOG_LEVEL_INFO then
        log_emit(" INFO", msg)
    end
end


local function log_error(msg)
    if LOG_LEVEL >= LOG_LEVEL_ERROR then
        log_emit("*ERROR", msg)
    end
end


local function log_throw_error(msg)
    log_error(msg)
    error(msg)
end


local function log_debug(msg)
    if LOG_LEVEL >= LOG_LEVEL_DEBUG then
        log_emit(" DEBUG", msg)
    end
end

local function log_fine(msg)
    if LOG_LEVEL >= LOG_LEVEL_FINE then
        log_emit(" FINE", msg)
    end
end

local function trim(s)
  return s:match "^%s*(.-)%s*$"
end


local function rewind(path, i, n)
    if n == nil or n == 1 then
        i = i - 1
        return string.sub(path, i, i), i
    else
        i, n = i - n, i - (n - 1)
        return string.sub(path, i, n), i
    end
end


local function collect(path, i, n)
    i = i + 1
    if n == nil or n == 1 then
        return string.sub(path, i, i), i
    else
        return string.sub(path, i, i + (n - 1)), i
    end
end


local function collect_ident(path, i, sep, with_ident)
    path_len = string.len(path)

    local c = nil
    local buf = {""}
    local sep_is_table = type(sep) == JP_TYP_TABLE
    if not sep_is_table then
        sep = {sep}
    end

    local _sep = {}
    for k, v in pairs(sep) do
        _sep[v] = true
    end
    sep = _sep

    while true do
        c, i = collect(path, i)
        log_debug("    [" .. i .. "] = " .. c)
        if sep[c] then
            if with_ident then
                table.insert(buf, c)
            end
            break
        end
        table.insert(buf, c)
        if i >= path_len then
            break
        end
    end
    log_debug("    RES: " .. table.concat(buf, ""))
    return table.concat(buf, ""), i
end


local function concat(current, tokens)
    res = {}
    for _, token in ipairs(tokens) do
        table.insert(res, token["token"])
    end
    table.insert(res, current)
    return table.concat(res, TOKEN_DELIM)
end


local function parse_jsonpath(path)
    local path_len = string.len(path)

    local tokens = {}
    local bracket_depth = 0

    local BRACKET_STATE = JP_STATE_NONE
    local QUOTE_STATE = JP_STATE_NONE
    local FILTER_STATE = JP_STATE_NONE

    local h, i, j = 0, 0, 0
    local pre, cur, nxt = nil, nil, nil
    local last_delim_i = 0
    local token_ = {}
    repeat
        local do_insert = true

        cur, i = collect(path, i)
        if i <= 0 then
            pre, h = JP_UNDEFINED, JP_UNDEFINED
        else
            pre, h = rewind(path, i)
        end
        if i >= path_len then
            nxt, j = JP_UNDEFINED, JP_UNDEFINED
        else
            nxt, j = collect(path, i)
        end

        log_debug("pre pre: " .. string.format("%s", pre) .. "[" .. string.format("%s", h) .. "]")
        log_debug("pre cur: " .. cur .. "[" .. i .. "]")
        log_debug("pre nxt: " .. string.format("%s", nxt) .. "[" .. string.format("%s", j) .. "]")

        if cur == JP_TOKEN_DELIM then
            log_debug("got a token delim")

            if BRACKET_STATE == JP_STATE_NONE and QUOTE_STATE == JP_STATE_NONE and FILTER_STATE == JP_STATE_NONE then
                log_debug("total none state")

                if pre ~= JP_TOKEN_DELIM then

                    local token = table.concat(token_)
                    log_debug("completed token: " .. token)

                    table.insert(tokens, token)
                    token_ = {}

                    do_insert = false
                end

            end

        elseif cur == JP_TOKEN_BRACKET_OPEN then

            if bracket_depth == 0 then
                bracket_depth = 1
                BRACKET_STATE = JP_STATE_IN_BRACKET
            else
                bracket_depth = bracket_depth + 1
            end

        elseif cur == JP_TOKEN_BRACKET_CLOSE then

            if BRACKET_STATE == JP_STATE_IN_BRACKET and bracket_depth == 1 then
                BRACKET_STATE = JP_STATE_NONE
            end
            bracket_depth = bracket_depth - 1

        elseif cur == JP_TOKEN_QUOTE then

            if pre ~= JP_TOKEN_ESCAPE then

                -- quotes preceeded by dots and open brackets will change state
                if QUOTE_STATE == JP_STATE_NONE and
                   (pre == JP_TOKEN_DELIM or pre == JP_TOKEN_BRACKET_OPEN) then

                    QUOTE_STATE = JP_STATE_IN_QUOTE

                -- quotes followed by dots and close brackets will change state
                elseif QUOTE_STATE == JP_STATE_IN_QUOTE and
                       (nxt == JP_TOKEN_BRACKET_CLOSE or nxt == JP_TOKEN_DELIM) then

                    QUOTE_STATE = JP_STATE_NONE

                end

            end

        elseif cur == JP_TOKEN_FILTER_CLOSE and
               pre ~= JP_TOKEN_ESCAPE and
               FILTER_STATE == JP_STATE_IN_FILTER then

            FILTER_STATE = JP_STATE_NONE

        elseif (cur == JP_TOKEN_FILTER or cur == JP_TOKEN_FILTER_OPEN) and
               pre ~= JP_TOKEN_ESCAPE and
               FILTER_STATE == JP_STATE_NONE and
               QUOTE_STATE == JP_STATE_NONE then

            FILTER_STATE = JP_STATE_IN_FILTER

        end

        if cur ~= nil and string.len(cur) > 0 and do_insert then
            log_debug("insert into token_: " .. cur)
            table.insert(token_, cur)
        end

    until i > path_len

    local token = table.concat(token_)
    log_debug("completed token: " .. token)
    table.insert(tokens, token)

    return tokens

end


-- kinda annoying that this has to be done in order to keep the parse function out of the global
--   scope and enable reuse
-- TODO: try to find a better way, perhaps ordering functions differently or breaking them up
local parse = function() end


local function parse_filter(filter)
    --[[
    A JSONPathFilter structure looks like this:
    {
        filter     = "@.author == 'Philip K. Dick'",
        negate     = <boolean>,
        subject    = "@.author",
        operator   = "==",
        predicate  = "Philip K. Dick",
        subj_nodes = {
            <JSONPathNode> [, ...]
        },
    }
    --]]

    local jsonpath_filter = {
        ["filter"] = filter,
        ["type"] = JP_TYPE_EXISTENCE,
    }

    local first_char = string.sub(filter, 1, 1)
    local second_char = string.sub(filter, 2, 2)
    local last_char = string.sub(filter, -1)
    if first_char == JP_TOKEN_FILTER and second_char == JP_TOKEN_FILTER_OPEN and last_char == JP_TOKEN_FILTER_CLOSE then
        filter = string.sub(filter, 3, -2)
    elseif first_char == JP_TOKEN_FILTER_OPEN and last_char == JP_TOKEN_FILTER_CLOSE then
        filter = string.sub(filter, 2, -2)
    else
        return nil
    end

    local found_idx, operator_len, subject, operator, predicate
    local negate = false
    for _, op in ipairs(operators) do
        found_idx = string.find(filter, op, 1, true)
        if found_idx ~= nil then
            operator_len = string.len(op)
            operator = string.sub(filter, found_idx, found_idx + operator_len - 1)
            if operator == op then
                subject = trim(string.sub(filter, 1, found_idx - 1))
                predicate = trim(string.sub(filter, found_idx + operator_len))
                jsonpath_filter["type"] = JP_TYPE_CONDITIONAL
                break
            end
            found_idx = nil
        end
    end

    if found_idx == nil then
        subject = filter
    end

    log_debug("subject: '" .. tostring(subject) .. "'")
    log_debug("operator: '" .. tostring(operator) .. "'")
    log_debug("predicate: '" .. tostring(predicate) .. "'")

    subj_first_char = string.sub(subject, 1, 1)
    if subj_first_char == JP_OP_NOT then
        negate = true
        subject = string.sub(subject, 2, -1)
    end

    jsonpath_filter["negate"] = negate
    jsonpath_filter["subject"] = subject
    jsonpath_filter["operator"] = operator
    jsonpath_filter["predicate"] = predicate
    jsonpath_filter["subj_nodes"] = parse(subject)

    return jsonpath_filter
end

local function parse_slice(slice)
    local slc_start, slc_end, slc_step = 0, -1, 1
    local _start, _end, _step = nil, nil, nil

    _start, _end, _step = string.match(slice, "([%-%d]*):([%-%d]*):([%-%d]*)")
    if _start ~= nil and _end ~= nil and _step ~= nil then
        if _start ~= "" then
            slc_start = tonumber(_start)
        end

        if _end ~= "" then
            slc_end = tonumber(_end)
        end

        if _step ~= "" then
            slc_step = tonumber(_step)
        end
    else
        _start, _end = string.match(slice, "([%-%d]*):([%-%d]*)")
        if _start ~= nil and _end ~= nil then
            if _start ~= "" then
                slc_start = tonumber(_start)
            end

            if _end ~= "" then
                slc_end = tonumber(_end)
            end
        else
            _idx = string.match(slice, "([%-%d" .. JP_TOKEN_WILDCARD_MATCH_PATTERN .. "]+)")
            if _idx ~= nil then
                if _idx ~= JP_TOKEN_WILDCARD then
                    slc_start = tonumber(_idx)
                    slc_end = nil
                    slc_step = nil
                end
            else
                log_throw_error("failed to parse slice")
            end
        end
    end

    return slc_start, slc_end, slc_step

end

local function parse_node(path, token)
    --[[
    A JSONPathNode structure looks like this:
    {
        path      = "$.store.book[(@.author == 'Philip K. Dick')]",
        token     = "book[(@.author == 'Philip K. Dick')]",
        type      = <JP_TYP_*>,
        recurse   = <boolean>,
        filters   = {
            <JSONPathFilter> [, ...]
        }
        slc_start = nil,
        slc_end   = nil,
        slc_step  = nil,
    }
    --]]
    local token_len = string.len(token)
    local filters = {}
    local node = {
        ["path"] = path,
        ["token"] = token,
        ["type"] = JP_TYPE_DEFAULT,
    }

    if token == JP_TOKEN_ROOT then
        node["type"] = JP_TYPE_ROOT
        return node
    end

    if token == JP_TOKEN_CONTEXT_ROOT then
        node["type"] = JP_TYPE_CONTEXT_ROOT
        return node
    end

    if string.sub(token, 1, 1) == "." then
        node["recurse"] = true
    else
        node["recurse"] = false
    end

    local token_node, i = collect_ident(token, 0, JP_TOKEN_BRACKET_OPEN)
    node["subject"] = token_node

    if i >= token_len then
        return node
    end
    log_debug("Token Node: " .. token_node .. " [" .. i .. "]")

    local subscript = string.sub(token, i + 1, -2)

    local filters = parse_filter(subscript)
    if filters ~= nil then
        node["filters"] = filters
        node["type"] = JP_TYPE_FILTER
        return node
    end

    local slc_start, slc_end, slc_step = parse_slice(subscript)
    if slc_start ~= nil then
        if slc_end == nil and slc_step == nil then
            node["slc_start"] = slc_start
            node["type"] = JP_TYPE_INDEXED
        else
            node["slc_start"] = slc_start
            node["slc_end"] = slc_end
            node["slc_step"] = slc_step
            node["type"] = JP_TYPE_SLICE
        end
        return node
    else
        error("failed to parse slice")
    end

end


local function parse(path)
    path = trim(path)

    if path_cache[path] ~= nil then
        log_debug("Using path from cache: " .. path)
        return path_cache[path]
    end

    local path_len = string.len(path)

    if path == nil or path_len <= 0 then
        log_throw_error("JSONPath expression nil or zero length")
    end

    local tokens = parse_jsonpath(path)

    local nodes = {}
    local jsonpath = {
        ["path"] = path,
        ["tokens"] = tokens,
    }

    local token_trail = {}
    for _, token in ipairs(tokens) do
        table.insert(token_trail, token)
        table.insert(nodes, parse_node(table.concat(token_trail, JP_TOKEN_DELIM), token))
    end

    jsonpath["nodes"] = nodes

    path_cache[path] = jsonpath
    return jsonpath
end


local function find(json_path, json_obj)
    local json_path_type = type(json_path)
    local json_obj_type = type(json_obj)

    if json_path_type == JP_TYPE_STRING then
        json_path = parse(json_path)
    elseif json_path_type ~= JP_TYPE_TABLE then
        error("expecting string or JSONPath (table) for json_path")
    end

    if json_obj_type ~= JP_TYP_TABLE then
        error("expecting table for json_obj")
    end

    local results = {}
    local _find = function(json_path, json_obj)

        for _, node in ipairs(json_path) do
            -- TODO: implement the find code
        end

    end

    _find(json_path, json_obj)

    return results

end


local function dump(...)
    print(DataDumper(...), "\n---")
end


local function compile_jsonpath(path)
    print(path)
    -- parts = split(path)
    parts = parse(path)
    dump(parts)
end


local function main()
    local json_file = "./search.json"
    local json_fh = assert(io.open(json_file, "r"))
    local json_ok, json_obj
    if json_fh then
        json_ok, json_obj = pcall(json.decode, json_fh:read("*a"))
        json_fh:close()
    end

    local json_paths = {
        "$.store.book[*].author",   -- authors of all books in the store
        "$..author",                -- all authors
        "$.store.*",                -- all things in store
        "$.store..price",           -- the price of everything in the store
        "$..book[2]",               -- the third book
        "$.store.book[(@.author == 'Philip K. Dick')].title",  -- all book titles by Philip K. Dick
        "$..book[-1]",              -- the last book
        "$..book[1:]",              -- skip the first book
        "$..book[0:-1:2]",          -- every other book
        "$..book[::2]",             --    ""   ""
        "$..book[0:1]",             -- the first two books
        "$..book[:1]",              --    ""   ""
        "$..book[(@.isbn-13)]",     -- all books with an isbn-13 number
        "$..book[(!@.isbn-13)]",    -- all books WITHOUT an isbn-13 number
        "$..book[(@.price < 10)]",  -- all books cheaper than 10
        "$..book[(@.price < 10)]",  -- testing cache
        "$..*",                     -- everything
    }

    -- parse("$.store.book[$(@.author == 'J. K. Rowling')]")
    -- parse("$.store.book[1:-1]")
    for index, path in ipairs(json_paths) do
        find(path, json_obj)
    end

end

main()
