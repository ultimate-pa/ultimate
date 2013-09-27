package RTconsistency;

import pea.*;

public class CDDx {


    
	public static void main(String[] args) 
	{
		System.out.println( RangeDecision.create( "c", RangeDecision.OP_GT, 1 ).and( RangeDecision.create( "c", RangeDecision.OP_LT,2 ) ) );
	}
}
