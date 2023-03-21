namespace C0deine

inductive C0Result
| return (i : UInt32)
| arith_error
| mem_error
| abort
