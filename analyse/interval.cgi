TYPE

// bot = -infini et top = +infini
  ConstFlattened    = flat(snum)
// bot = (top, bot) et top = (bot, top)
  Interval          = ConstFlattened * ConstFlattened
  ListConstFlattened= list(ConstFlattened)
  State             = Var -> Interval

PROBLEM Interval_Analysis

  direction  : forward
  carrier    : State
  init       : bot
  init_start : [-> (bot, top)]
  combine    : join


TRANSFER

// in assignments calculate the new value of the variable and add it to the state
  ASSIGN(variable, expression) = 
      @\[variable -> evalAExp(expression, @)]

// in procedur calls pass the value of the actual argument to the formal parameter
  CALL(_, param, exp), call_edge = 
      @\[param -> evalAExp(exp, @)]

  CALL(_, _, _), local_edge = bot


// at the end of procedures reset the formal parameter
  END(_, param) =
      @\[param -> top]

// test conditions
IF(expression), true_edge = branch(expression, @, true)

IF(expression), false_edge = branch(expression, @, false)

// loop conditions
WHILE(expression), true_edge = branch(expression, @, true)

WHILE(expression), false_edge = branch(expression, @, false)

SUPPORT

  join :: State * State -> State
  join(a, b) = crunch(a, b, join_int)

  join_int :: Interval * Interval -> Interval
  join_int(i1, i2) = let min1 = i1#1,
			 min2 = i2#1,
			 max1 = i1#2,
			 max2 = i2#2 in 
                         if (max1 = bot) then i2 else if (max2 = bot) then i1
			 else if (min1 = bot) || (min2 = bot) then if (max1 = top) || (max2 = top) then (bot, top)
			                                           else if drop(max1) < drop(max2) then (bot, max2) 
                                                                        else (top, max1)
                                                                        endif
			                                           endif
		              else if (max1 = top) || (max2 = top) then if drop(min1) < drop(min2) then (min1, top) 
                                                                        else (min2, top)
                                                                        endif
			           else (findmin(min1, [min1,min2]), findmax(max1, [max1,max2]))
			           endif
			      endif
			 endif endif


  evalAExp :: Expression * State -> Interval
  evalAExp(expression, state) =
    case expType(expression) of
      "ARITH_BINARY" => case expOp(expression) of
        "+" => let valLeft  = evalAExp(expSubLeft(expression),  state),
                   valRight = evalAExp(expSubRight(expression), state) in
               addabstract(valLeft, valRight);
        "-" => let valLeft  = evalAExp(expSubLeft(expression),  state),
                   valRight = evalAExp(expSubRight(expression), state) in
               subabstract(valLeft, valRight);
        "*" => let valLeft  = evalAExp(expSubLeft(expression),  state),
                   valRight = evalAExp(expSubRight(expression), state) in
               multabstract(valLeft, valRight);
	"/" => let valLeft  = evalAExp(expSubLeft(expression),  state),
                   valRight = evalAExp(expSubRight(expression), state) in
               divabstract(valLeft, valRight);
        endcase;
      "ARITH_UNARY" =>
	case expOp(expression) of
          "-" => let value = evalAExp(expSub(expression), state) in
                 subabstract((lift(0),lift(0)), value);
        endcase;
     
      "VAR"   => state ( expVar(expression) );
      "CONST" => (lift(expVal(expression)),lift(expVal(expression)));
      _       => error("Runtime Error: evalAExp applied to nonarithmetic Expression");
    endcase


    addabstract :: Interval * Interval -> Interval
    addabstract(i1, i2) = let min1 = i1#1,
			      min2 = i2#1,
			      max1 = i1#2,
			      max2 = i2#2 in
			      if (max1 = bot) || (max2 = bot) then (top, bot)
			      else if (min1 = bot) || (min2 = bot) then if (max1 = top) || (max2 = top) then (bot, top)
			                                                else (bot, lift(drop(max1)+drop(max2))) 
			                                                endif
		                   else if (max1 = top) || (max2 = top) then (lift(drop(min1)+drop(min2)), top)
			                else (lift(drop(min1)+drop(min2)), lift(drop(max1)+drop(max2)))
			                endif
			           endif
			      endif


    subabstract :: Interval * Interval -> Interval
    subabstract(i1, i2) = let min1 = i1#1,
			      min2 = i2#1,
			      max1 = i1#2,
			      max2 = i2#2 in
			      if (max1 = bot) || (max2 = bot) then (top, bot)
			      else if (min1 = bot) || (max2 = top) then if (max1 = top) || (min2 = bot) then (bot, top)
			                                                else (bot, lift(drop(max1)-drop(min2))) 
			                                                endif
		                   else if (max1 = top) || (min2 = bot) then (lift(drop(min1)-drop(max2)), top)
			                else (lift(drop(min1)-drop(max2)), lift(drop(max1)-drop(min2)))
			                endif
			           endif
			      endif


    multabstract :: Interval * Interval -> Interval
    multabstract(i1, i2) = let min1 = i1#1,
			       min2 = i2#1,
			       max1 = i1#2,
			       max2 = i2#2 in
                           if (max1 = bot) || (max2 = bot) then (top, bot)
                           else let option1 = multaux(min1, min2),
                                    option2 = multaux(min1, max2),
                                    option3 = multaux(max1, min2),
                                    option4 = multaux(max1, max2) in
                                let nmin = findmin(option1, [option1, option2, option3, option4]),
                                    nmax = findmax(option1, [option1, option2, option3, option4]) in
                                (nmin, nmax)
                           endif



    multaux :: ConstFlattened * ConstFlattened -> ConstFlattened
    multaux(x, y) = if x = top then if y = top then top else if y = bot then bot else if drop(y) < 0 then bot else if drop(y) > 0 then top else lift(0) endif endif endif endif 
                    else if x = bot then if y = top then bot else if y = bot then top else if drop(y) < 0 then top else if drop(y) > 0 then bot else lift(0) endif endif endif endif 
                         else if drop(x) < 0 then if y = top then bot else if y = bot then top else lift(drop(y)*drop(x)) endif endif
			      else if drop(x) > 0 then if y = top then top else if y = bot then bot else lift(drop(y)*drop(x)) endif endif
                                   else lift(0)
                                   endif
                              endif
                         endif
                    endif


    divabstract :: Interval * Interval -> Interval
    divabstract(i1, i2) = let  min1 = i1#1,
			       min2 = i2#1,
			       max1 = i1#2,
			       max2 = i2#2 in
                           if (max1 = bot) || (max2 = bot) then (top, bot) else
                           if (min2 != bot) && (drop(min2) = 0) then
				if max2 = top then
					if (min1 != bot) && (drop(min1)>=0) then (lift(0), top) 
					else if (max1 != top) && (drop(max1) <= 0) then (bot, lift(0))
					     else (bot, top)
					     endif
					endif
				else    if (drop(max2) = 0) then (top, bot)
					else    if (min1 != bot) && (drop(min1)>=0) then (lift(drop(min1)/drop(max2)), top)
						else if (max1 != top) && (drop(max1) <= 0) then (bot, lift(drop(max1)/drop(max2)))
						     else (bot, top)
						     endif
						endif
					endif
				endif
			   else if (max2 != top) && (drop(max2) = 0) then 
					if min2 = bot then 
						if (min1 != bot) && (drop(min1)>=0) then (bot, lift(0)) 
						else if (max1 != top) && (drop(max1) <= 0) then (lift(0), top)
						     else (bot, top)
						     endif
						endif
					else    if (drop(min2) = 0) then (top, bot)
						else    if (min1 != bot) && (drop(min1)>=0) then (bot, lift(drop(min1)/drop(min2)))
							else if (max1 != top) && (drop(max1) <= 0) then (lift(drop(max1)/drop(min2)), top)
							     else (bot, top)
							     endif
							endif
						endif
					endif
				else
					if ((min2 = bot) || (drop(min2) < 0)) && ((max2 = top) || (drop(max2) > 0)) then (bot, top)
					else
						let option1 = divaux(min1, min2),
				                    option2 = divaux(min1, max2),
				                    option3 = divaux(max1, min2),
				                    option4 = divaux(max1, max2) in
				                let nmin = findmin(option1, [option1, option2, option3, option4]),
				                    nmax = findmax(option1, [option1, option2, option3, option4]) in
				                (nmin, nmax)
					endif
				endif	
                           endif endif
    
    divaux :: ConstFlattened * ConstFlattened -> ConstFlattened
    divaux(n1, n2) = if (n2 = top) || (n2 = bot) then lift(0) else if (n1 = top) || (n1 = bot) then multaux(n1, n2) else lift(drop(n1)/drop(n2)) endif endif


    findmin :: ConstFlattened * ListConstFlattened -> ConstFlattened
    findmin(x, l) = if x = bot then bot 
                    else case l of
		           [] => x;
		           e:lprime =>  if e = bot then 
						bot
					else
						if e = top then
							findmin(x, lprime)
						else
							if x = top then
								findmin(e, lprime)
							else
								if drop(x) <= drop(e) then
									findmin(x, lprime)
								else
									findmin(e, lprime)
								endif
							endif
						endif
					endif;
			    endcase
                    endif

    findmax :: ConstFlattened * ListConstFlattened -> ConstFlattened
    findmax(x, l) = if x = top then top 
                    else case l of
		           [] => x;
		           e:lprime =>  if e = top then 
						top
					else 
						if e = bot then 
							findmax(x, lprime)
						else 
							if x = bot then
								findmax(e, lprime)
							else
								if drop(x) <= drop(e) then
									findmax(e, lprime)
								else 
									findmax(x, lprime)
								endif
							endif
						endif
					endif;
			    endcase
                    endif

    evalConst :: Expression -> bool
    evalConst(expression) =let Left = expSubLeft(expression),
			       Right  =  expSubRight(expression) in
      case expType(expression) of
        "BOOL_BINARY" => case expOp(expression) of 
          "<" => expVal(Left) < expVal(Right); 
          "<=" => expVal(Left) <= expVal(Right); 
          ">" => expVal(Left) > expVal(Right); 
          ">=" => expVal(Left) >= expVal(Right); 
          "=" => expVal(Left) = expVal(Right); 
          "<>" => expVal(Left) != expVal(Right);
          endcase;
        _ => false;
      endcase


    branch :: Expression * State * bool -> State
    branch(expression, state, edge) =
	if edge then 
	      case expType(expression) of
		"TRUE" => state;
		"FALSE" => bot;
		"BOOL_UNARY" => branch(expSub(expression), state, false);
		"BOOL_BINARY" => let Left = expSubLeft(expression),
			     	     Right  =  expSubRight(expression) in
		  if (expType(Left) = "CONST") && (expType(Right) = "CONST") then
		  	  if evalConst(expression) then state else bot endif
		  else
			  case expOp(expression) of 
			  "<" => lower(Left, Right, state);
			  "<=" => lowerequal(Left, Right, state);
			  ">" => lower(Right, Left, state);
			  ">=" => lowerequal(Right, Left, state);
			  "=" => testequal(Left, Right, state);					
			  "<>" => state;
			  endcase
		  endif;
		_ => state;
	      endcase
	else
	      case expType(expression) of
		"TRUE" => bot;
		"FALSE" => state;
		"BOOL_UNARY" => branch(expSub(expression), state, true);
		"BOOL_BINARY" => let Left = expSubLeft(expression),
			     	     Right  =  expSubRight(expression) in
		  if (expType(Left) = "CONST") && (expType(Right) = "CONST") then
		  	  if evalConst(expression) then bot else state endif
		  else
			  case expOp(expression) of 
			  ">=" => lower(Left, Right, state);
			  ">" => lowerequal(Left, Right, state);
			  "<=" => lower(Right, Left, state);
			  "<" => lowerequal(Right, Left, state);
			  "<>" => testequal(Left, Right, state);				
			  "=" => state;
			  endcase
		  endif;
		_ => state;
	      endcase
	endif


    intersection :: Interval * Interval -> Interval 
    intersection(i1, i2) = let new_max = findmin(i1#2, [i1#2, i2#2]),
			       new_min = findmax(i1#1, [i1#1, i2#1]) in
			   if new_max = bot then (top, bot) 
			   else
				   if (findmin(new_max, [new_max, new_min]) = bot) then (new_min, new_max) 
				   else 
					if drop(findmin(new_max, [new_max, new_min])) = drop(new_min) then (new_min, new_max) 
					else (top, bot) 
					endif
				   endif
			   endif


    testequal :: Expression * Expression * State -> State
    testequal(Left, Right, state) = if expType(Left) = "VAR" then 
					if expType(Right) = "VAR" then
						let i1 = state(expVar(Left)),
						    i2 = state(expVar(Right))in
						state\[expVar(Left) -> intersection(i1, i2), expVar(Right) -> intersection(i1, i2)]
					else
						let i1 = state(expVar(Left)),
						    i2 = evalAExp(Right, state) in
						state\[expVar(Left) -> intersection(i1, i2)]
					endif
				else 
					if expType(Right) = "VAR" then
						let i1 = evalAExp(Left, state),
						    i2 = state(expVar(Right)) in
						state\[expVar(Right) -> intersection(i1, i2)]
					else
						state
					endif
				endif


    lowerequal :: Expression * Expression * State -> State
    lowerequal(Left, Right, state) = if expType(Left) = "VAR" then 
					if expType(Right) = "VAR" then
						let i1 = state(expVar(Left)),
						    i2 = state(expVar(Right))in
						state\[expVar(Left) -> intersection(i1, (bot, findmax(i2#2, [i2#2, i2#1]))),
						       expVar(Right) -> intersection((findmin(i1#1, [i1#1, i1#2]), top), i2)]
					else
						let i1 = state(expVar(Left)),
						    i2 = evalAExp(Right, state) in
						state\[expVar(Left) -> intersection(i1, (bot, findmax(i2#2, [i2#2, i2#1])))]
					endif
				    else 
					if expType(Right) = "VAR" then
						let i1 = evalAExp(Left, state),
						    i2 = state(expVar(Right)) in
						state\[expVar(Right) -> intersection((findmin(i1#1, [i1#1, i1#2]), top), i2)]
					else
						state
					endif
				    endif
				
    lower :: Expression * Expression * State -> State
    lower(Left, Right, state) = if expType(Left) = "VAR" then 
					if expType(Right) = "VAR" then
						let i1 = state(expVar(Left)),
						    i2 = state(expVar(Right)) in
						let i1p1 = addabstract(i1, (lift(1), lift(1))),
						    i2m1 = subabstract(i2, (lift(1), lift(1))) in
						state\[expVar(Left) -> intersection(i1, (bot, findmax(i2m1#2, [i2m1#2, i2m1#1]))),
						       expVar(Right) -> intersection((findmin(i1p1#1, [i1p1#1, i1p1#2]), top), i2)]
					else
						let i1 = state(expVar(Left)),
						    i2 = evalAExp(Right, state) in
						let i2m1 = subabstract(i2, (lift(1), lift(1))) in
						state\[expVar(Left) -> intersection(i1, (bot, findmax(i2m1#2, [i2m1#2, i2m1#1])))]
					endif
				    else 
					if expType(Right) = "VAR" then
						let i1 = evalAExp(Left, state),
						    i2 = state(expVar(Right)) in
						let i1p1 = addabstract(i1, (lift(1), lift(1))) in
						state\[expVar(Right) -> intersection((findmin(i1p1#1, [i1p1#1, i1p1#2]), top), i2)]
					else
						state
					endif
				    endif
				
  
