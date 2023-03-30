open("strings.idr", "w") do io
    println(io, "string : String")
    print(io, "string = \"")
    # Ascii
    for c in 0:127
        print(io, "\\x" * string(c, base = 16))
    end
    println(io, "\"")
    println(io, "main : IO ()")
    println(io, "main = printLn \$ length string")
end
