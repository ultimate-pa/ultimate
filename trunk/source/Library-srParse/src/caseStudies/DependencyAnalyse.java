package caseStudies;

import srParse.*;
import pea.Phase;
import pea.RangeDecision;
import pea.PhaseEventAutomata;
import java.util.*;
import pea.CDD;
import PatternLanguage.PL_initiatedPattern;

public class DependencyAnalyse {
	
	private Vector<String> clocks;
	private Vector<Vector<Phase>> phases;
	
	public DependencyAnalyse()
	{
		clocks=new Vector<String>();
		phases=new Vector<Vector<Phase>>();
	}
	
	private int indexOf( String clk )
	{
		int res = clocks.indexOf( clk );
		if( res<0 )
		{
			if( clocks.add(clk) )
			{
				res=clocks.size();
				phases.add( new Vector<Phase>() );
			}
		}
		return res;
	}
	
	private void extractClocks( Phase p, CDD ci)
	{
		if( ci!=null &&  ci!=CDD.FALSE && ci!=CDD.TRUE )
		{
			if( ci.decision instanceof RangeDecision )
			{
				RangeDecision rd=(RangeDecision)ci.decision;
				int idx=indexOf( rd.getVar() );
				if( idx>=0 )
				{
					phases.elementAt(idx).add( p );
				}
			}
			extractClocks( p, ci.getChilds()[0] );
			extractClocks( p, ci.getChilds()[1] );
		}
	}
	
	public void createDependencys( PhaseEventAutomata pea )
	{
		int i;
		for( i=0;i<pea.getPhases().length;i++)
		{
			CDD ci=pea.getPhases()[i].getClockInvariant();
			extractClocks( pea.getPhases()[i], ci );			
		}
	}
	
	private Set<String> getSubExpressions( CDD cdd)
	{
		Set<String> res=new HashSet<String>();
		
		if( cdd!=CDD.FALSE && cdd!=CDD.TRUE && cdd!=null )
		{
			res.add(cdd.getDecision().getVar());
			for(int i=0;i<cdd.getChilds().length;i++)
			{
				res.addAll( getSubExpressions( cdd.getChilds()[i] ) );
			}
		}
		
		return res;
	}
	
	private boolean hasCommonElems( Set<srParsePattern> set1, Set<srParsePattern> set2 )
	{
		Iterator<srParsePattern> it=set1.iterator();
		Set<String> vars=new HashSet<String>();
		Set<String> vars2=new HashSet<String>(); 
		while( it.hasNext() )
		{
			srParsePattern pat=it.next();
			vars.addAll( getSubExpressions( pat.getScope().getCdd1() ) );
			vars.addAll( getSubExpressions( pat.getScope().getCdd2() ) );
			
			for(int i=0;i<pat.getCdds().size();i++ )
			{
				vars.addAll( getSubExpressions( pat.getCdds().get(i) ) );
			}
		}
		
		
		it=set2.iterator();
		while( it.hasNext() )
		{
			srParsePattern pat=it.next();
			vars2.addAll( getSubExpressions( pat.getScope().getCdd1() ) );
			vars2.addAll( getSubExpressions( pat.getScope().getCdd2() ) );
			
			for(int i=0;i<pat.getCdds().size();i++ )
			{
				vars2.addAll( getSubExpressions( pat.getCdds().get(i) ) );
			}
		}
		
		Iterator<String> it2=vars.iterator();
		
		while(it2.hasNext() )
		{
			String var=it2.next();
			
			if( !vars2.add(var))
				return true;
		}
		
		return false;
	}
	
	/*public Vector<Set<srParsePattern>> patternAnalysis2( Vector<srParsePattern> patterns )
	{
		while
	}*/
	
	public Vector<Vector<srParsePattern>> patternAnalysis( Vector<srParsePattern> patterns )
	{
		Vector<Vector<srParsePattern>> res=new Vector<Vector<srParsePattern>>();
		int[] ht=new int[10000];
		int curr;
		boolean changed=true;
		int ccnt=0;
		
		int i;
		while( patterns.size()>0 )
		{
			res.add( new Vector<srParsePattern>() );
			curr=res.size()-1;
			ccnt=0;
			
			for(i=0;i<10000;i++ )
				ht[i]=0;
			
			changed=true;
			while(changed)
			{
				changed=false;
				i=0;
				while(i<patterns.size())
				{
					int j;
					boolean add=false;
					
					Vector<Integer> hs=patterns.get(i).getElemHashes();
					for(j=0;j<hs.size();j+=2)
					{
						int val1=hs.get(j).intValue();
						int val2=hs.get(j+1).intValue();
						val1*=(val1>=0)?1:-1;
						val2*=(val2>=0)?1:-1;
						int idx1=(val1 /32 )%10000;
						int msk1=1<<(val1 % 32);
						int idx2=(val2 /32)%10000;
						int msk2=1<<(val2 % 32);
						if( ( ( ht[idx1] & msk1 )!=0 && ( ht[idx2] & msk2 )!=0 ) || ccnt==0 ) // übereinstimmung eines teilausdrucks oder filter ist leer
						{
							res.get(curr).add( patterns.get(i) );
							patterns.remove(i);
							add=true;
							changed=true;
							ccnt++;
							break;
						}
					}
					
					if( add )
					{
						for(j=0;j<hs.size();j+=2)
						{
							int val1=hs.get(j).intValue();
							int val2=hs.get(j+1).intValue();
							
							val1*=(val1>=0)?1:-1;
							val2*=(val2>=0)?1:-1;
							int idx1=(val1 /32 )%10000;
							int msk1=1<<(val1 % 32);
							int idx2=(val2 / 32 ) %10000;
							int msk2=1<<(val2 % 32);
							ht[idx1]|=msk1;
							ht[idx2]|=msk2;
							
						}
					}
					else
						i++;
				}
			}
		}
		
		
		return res;
	}

}







