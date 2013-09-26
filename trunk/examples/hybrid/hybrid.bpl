procedure myProcedure() returns (){
	var globalClock, localClock, temperature : real;
	
	globalClock := 0.0;
	temperature := 1.0;
	
	while(true){
		Loc1:
			havoc localClock;
			assume (localClock >= 0.0);
			assume ((temperature + (1.0 * localClock)) <= 20.0);
			temperature := temperature + (1.0 * localClock);
			globalClock := globalClock + localClock;
			if(*){
				assume (temperature >= 10.0);
				goto Loc2;
			} else {
				goto End;
			}
		
		Loc2:
			havoc localClock;
			assume (localClock >= 0.0); 
			assume ((temperature + ((0.0 - 2.0) * localClock)) >= (0.0 - 10.0));
			temperature := temperature + ((0.0 - 2.0) * localClock);
			globalClock := globalClock + localClock;
			if(*){
				assume (temperature >= ( 0.0 - 5.0));
				goto Loc1;
			} else {
				goto End;
			}
	}
	End:
	assert (temperature <= 10.0);
}