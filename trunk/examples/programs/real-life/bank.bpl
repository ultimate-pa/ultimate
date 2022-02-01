
var isOverdraft : bool;

procedure main()
modifies isOverdraft;
 {
  var functionValue : int;
  var value : int;
  var balance : int;

    balance := 0;
	havoc functionValue;
    //while( read(file, &functionValue, sizeof(int))  > 0) {
      havoc value;
      if(functionValue > 0){

		if (value >= 0) {
			if (isOverdraft) {
				if(!(balance < 0)){
				  assert(false); // FAILURE!
				}
			  } else {
				  balance := balance - value;
				  if (balance < 0) {
					isOverdraft := true;
				  }
			  }
		}

      }  
      else if(functionValue <= 0){
		if (value >= 0) {
			balance := balance + value;
		}
      }
    //}
  }


