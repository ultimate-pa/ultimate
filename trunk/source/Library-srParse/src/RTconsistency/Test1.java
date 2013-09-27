package RTconsistency;


import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Vector;

import pea.CDD;
import pea.PhaseEventAutomata;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck4.GI;
import pea.*;
import java.util.*;


public class Test1 {
	
	Set<Integer> dphases[]; 
	int cnt=0;
	
	
	public Test1( Vector<PhaseEventAutomata> peas )
	{
		dphases=new Set[peas.size()];
		/*for(int i=0;i<dphases.length;i++ )
		{
			dphases[i]=new HashSet<Integer>();
		}*/
	}
	
	public void addDl( String dlName )
	{
		String[] states=dlName.split( "_X_" );
		for( int i=0;i<states.length;i++ )
		{
			Set<Integer> ls=new HashSet<Integer>();
			for(int j=0;j<states[i].length();j++ )
			{
				Integer buf=null;
				switch ((int)states[i].charAt(j))
				{
					case ((int)'0'):
					case ((int)'1'):
					case ((int)'2'):
					case ((int)'3'):
					case ((int)'4'):
					case ((int)'5'):
					case ((int)'6'):
					case ((int)'7'):
					case ((int)'8'):
					case ((int)'9'):
						buf=new Integer(states[i].charAt(j));
						buf-=48;
						if( j<states[i].length()-1 )	
						{
							if( states[i].charAt(j+1)=='W' )
							{
								buf+=10;
							}
						}
						break;
					default:
						break;
				}
				if( buf!=null )
					ls.add( buf );
			}
			
			if( cnt==0 )
			{
				dphases[i]=ls;
			}
			else
			{
				dphases[i].retainAll( ls );
			}
				
		}
		cnt++;
	}
	
	public void showCommon()
	{
		System.out.println( "Commen DC Phases in Deadlocks:" );
		
		for( int i=0;i<dphases.length;i++ )
		{
			if( dphases[i].size()>0 )
			{
				System.out.print( "PEA "+i+": " );
				Iterator<Integer> it=dphases[i].iterator();
				while( it.hasNext() )
				{
					Integer num=it.next();
					
					if( num>10 )
					{
						System.out.print( num%10 + "W " );
					}
					else
					{
						System.out.print( num + " " );
					}
				}
				System.out.println( "" );
			}
		}
	}
}



