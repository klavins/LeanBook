--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

/- # Integers via Quotients

Now that we have defined the natural numbers `Nat`, the next obvious step is to define the integers `Int`(whole numbers that can be positive, negative or zero) . This can be done in several ways. For example, the Lean 4 standard library defines integers inductively saying that (a) any natural number is an integer, and (b) the negative successor of an integer is an integer.

 -/
