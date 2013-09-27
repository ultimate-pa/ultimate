package RTconsistency;

import java.io.BufferedReader;
import java.io.FileReader;

public class Z3eval {
	
	static final int limit=660;
	static final String filename="C:\\daten\\test1\\New Folder (2)\\accreqs1.req";
	public static void main(String[] args) {
		try{
			int i;
			for(i=0;i<limit;i++)
			{
				BufferedReader rd = new BufferedReader( new FileReader( filename+"out12_"+i+"_.smt" ) );
				String ln=rd.readLine();
				while( ln!=null )
				{
					if( ln.equals("sat") )
					{
						System.out.println( filename+"out12_"+i+"_.smt" );
						break;
					}
					ln=rd.readLine();
				}
			}
		}catch (Exception e)
		{
			
		}
		
	}

}
