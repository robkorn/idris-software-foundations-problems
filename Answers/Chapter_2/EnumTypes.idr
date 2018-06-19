
module EnumTypes

data Day = Monday
          | Tuesday
          | Wednesday
          | Thursday
          | Friday
          | Saturday
          | Sunday
%name Day day, day1, day2

nextWeekday : Day -> Day
nextWeekday Monday = Tuesday
nextWeekday Tuesday = Wednesday
nextWeekday Wednesday = Thursday
nextWeekday Thursday = Friday
nextWeekday Friday = Saturday
nextWeekday Saturday = Sunday
nextWeekday Sunday = Monday


testNextWeekday : (nextWeekday (nextWeekday Saturday)) = Monday
testNextWeekday = Refl
