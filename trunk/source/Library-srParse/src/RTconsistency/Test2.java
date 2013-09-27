package RTconsistency;

import java.util.*;
import pea.*;

public class Test2 {
	
	Hashtable<String, Integer> clocks;
	
	public Test2()
	{
		clocks=new Hashtable<String, Integer>();
	}
	
	public void addCInv( CDD ci )
	{
		Vector<String> cl=getClocks( ci );
		
		for( int i=0;i< cl.size();i++ )
		{
			Integer old=clocks.get( cl.get(i) );
			if( old==null )
				old=new Integer(1);
			else
				old++;
			
			clocks.put( cl.get(i), old );	
		}
	}
	
	public void printRes()
	{
		Set<String> keys=clocks.keySet();
		Iterator<String> it=keys.iterator();
		Vector<ClCnt> clcnt=new Vector<ClCnt>();
		
		System.out.println( "Clocks in deadlockstates: " );
		while( it.hasNext() )
		{
			String k=it.next();
			Integer num=clocks.get( k );
			
			if( num!=null )
			{
				//System.out.println( k+": "+num );
				clcnt.add( new ClCnt( k, num ) );
			}
		}
		
		Collections.sort( clcnt );
		
		for(int i=0;i<clcnt.size();i++ )
		{
			ClCnt c=clcnt.get(i);
			System.out.println( c.clockname+": "+c.count );
		}
	}
	
	class ClCnt implements Comparable<ClCnt>
	{
		String clockname;
		int count=0;
		
		public int compareTo( ClCnt b )
		{
			return count-b.count;
		}
		
		public ClCnt( String clockname )
		{
			this.clockname=clockname;
		}
		
		public ClCnt( String clockname, int cnt )
		{
			this.clockname=clockname;
			count=cnt;
		}
	}
	
	private Vector<String> getClocks(CDD cdd)
	{
		Vector<String> res=new Vector<String>();
		
		if( cdd.getDecision()!=null && cdd.getDecision() instanceof RangeDecision )
		{
			res.add( cdd.getDecision().getVar() );
		}
		
		if( cdd.getChilds()==null )
			return res;
		
		
		for(int i=0;i<cdd.getChilds().length;i++)
		{
			res.addAll( getClocks(cdd.getChilds()[i]) );
		}
		
		return res;
	}

}
