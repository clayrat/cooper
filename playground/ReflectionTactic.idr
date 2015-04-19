module ReflectionTactic

%default total

data IsYes : (Dec a) -> Type where
  ItIsYes : IsYes (Yes prf)
  
getYes : (x:Dec a) -> IsYes x -> a
getYes (Yes prf) ItIsYes = prf
  
syntax reflectionTactic [parser] [decision] =
  quoteGoal goal by parser in
  getYes (decision goal) ItIsYes
