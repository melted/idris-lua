function boolint(b)
    if b then
        return 1
    end
    return 0
end

function sysinfo(i)
    if i == 0 then
        return "lua"
    end
    return ""
end
