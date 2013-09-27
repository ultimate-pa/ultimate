package RTconsistency;



/*
 *  Gleiche Idee wie Test1 nutzt aber in den PEA zusätzlich gespeicherte DC Phasen 
 *  Informationen 
 * 
 * 
 * Todo: nach Deadlocks suchen, die nur eine Zeitbeschränkte DC Phase enthalten 
 */


public class Test3 {
	int[] active;
	int[] waiting;
	int[] exact;
	
	public Test3( int peaCount )
	{
		active=new int[peaCount];
		waiting=new int[peaCount];
		exact=new int[peaCount];
		
		for(int i=0;i<peaCount;i++)
		{
			active[i]=0xffffffff;
			waiting[i]=0xffffffff;
			exact[i]=0xffffffff;
		}
	}
	
	public void addDl( int[] active, int[] waiting, int[] exact )
	{
		for( int i=0;i<this.active.length;i++ )
		{
			this.active[i]=this.active[i] & active[i];
			this.waiting[i]=this.waiting[i] & waiting[i];
			this.exact[i]=this.exact[i] & exact[i];
		}
	}
	
	public void printCommon()
	{
		String[] names=new String[active.length];
		for(int i=0;i<active.length;i++)
		{
			names[i]="PEA "+i;
		}
		printCommon( names );
	}
	
	public void printCommon( String[] names)
	{
		System.out.println( "Common DC Phases in Deadlock:" );
		
		String delim="_";
		for( int j=0;j<active.length;j++ )
		{
			System.out.print( names[j]+ ": ");
			if( active[j]!=0 )
			{
				int active=this.active[j];
				int exactbound=this.exact[j];
				int waiting=this.waiting[j];
				StringBuffer sb=new StringBuffer();
				for (int i = 0, bit = 1; bit <= active; i++, bit += bit) {
		            if ((active & bit) == 0)
		                continue;
		            sb.append(delim).append(i);
		            if ((exactbound & bit) != 0)
		                sb.append('X');
		            else if ((waiting & bit) != 0)
		                sb.append('W');
		            delim = "";
		        }
				System.out.println( sb );
			}
			else
				System.out.println( 0 );
		}
	}
}
