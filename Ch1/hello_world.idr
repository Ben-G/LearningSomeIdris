module Main

main : IO ()
main = putStrLn (cast 'x')

square : (x : Int) -> Int
square x = x * x

StringOrInt : Bool -> Type
StringOrInt x = case x of
                    True => Int
                    False => String

-- Return type of this function depends on return value
-- of the call to `StringOrInt`. Will be either Int or String
getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
                    True => 94
                    False => "Nintey Four"

-- Return value will always be String
valToString : (x : Bool) -> StringOrInt x -> String
-- Depending on the value that `StringOrInt` returns for `x`
-- We need / don't need to cast the return value
valToString x val = case x of
                        -- Return value was Int; cast
                        True => cast val
                        -- Return values was String, don't cast
                        False => val
