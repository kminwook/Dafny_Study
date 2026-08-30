datatype date = Date(day:nat, month:nat, year:nat)

function makeFirstOfJan(d : date) : date
{
  d.(day := 1, month := 1)
}

// what about a day-after function?
function nextday (d:date) : date
{
  if d.day == 31 then
    if d.month == 12 then
      d.(day := 1, month := 1, year:= d.year+1)
    else
      d.(day := 1, month:= d.month+ 1)
  else
    d.(day :=d.day+1)
}