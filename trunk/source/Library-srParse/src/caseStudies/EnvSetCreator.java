package caseStudies;

import pea.*;

import java.util.*;

public class EnvSetCreator {
	
	
	int num; // nummer der Menge
	int kenv; // es werden <= kenv vorgänger verwendet
	int size; // maximale größe größe einer einzelnen Menge
	
	Phase location;
	PhaseEventAutomata pea;
	
	public EnvSetCreator(PhaseEventAutomata pea, Phase location, int k, int n)
	{
		this.pea=pea;
		this.location=location;
		num=0;
		kenv=k;
		size=n;
	}
	
	/*
	public PhaseEventAutomata getNextEnvAutomata( )
	{
		int i;
		int k=-(size*num);
		Vector<Phase> phases=new Vector<Phase>();
		Vector<Phase> init=new Vector<Phase>();
		for(i=0;i<pea.getPhases().length;i++ )
		{
			int j;
			for( j=0;j<pea.getPhases()[i].getTransitions().size();j++ )
			{
				if( pea.getPhases()[i].getTransitions().get(j).getDest().equals(location) )
				{
					if( k>=0 )
					{
						phases.add(pea.getPhases()[i]);
						pea.getPhases()[i].isKernel=true;
					}
					k++;
				}
			}
			if( k>size )
				break;
		}
		
		for(i=0;i<pea.getPhases().length;i++ )
		{
			if( !pea.getPhases()[i].isKernel )
			{
				int j;
				for( j=0;j<pea.getPhases()[i].getTransitions().size();j++ )
				{
					if( pea.getPhases()[i].getTransitions().get(j).getDest().isKernel )
					{
						pea.getPhases()[i].getTransitions().get(j).getDest().isInit=true;
						init.add( pea.getPhases()[i].getTransitions().get(j).getDest() );
					}
				}
			}
		}
		
		int n;
		Phase catchAll=new Phase( "CatchAll" );
		//catchAll.addTransition( catchAll, CDD.TRUE, new String[0] );
		for( n=0;n<phases.size();n++ )
		{
			for(i=0;i<phases.get(n).getTransitions().size();i++) // unnötige transitionen entfernen
			{
				if( !phases.get(n).getTransitions().get(i).getDest().isKernel )
				{
					phases.get(n).getTransitions().get(i).setDest( catchAll );
					//phases.get(n).addTransition( catchAll, phases.get(n).getTransitions().get(i).getGuard(), new String[0] );
				}
			}
		}
		
		Vector<String> clocks= getClocks( pea );
		Vector<Phase> nonDetInit=new Vector<Phase>();
		Phase p,q;
		CDD invp;
		CDD invq=RangeDecision.create( clocks.get(0), RangeDecision.OP_LT, 10 );
		q=new Phase( clocks.get(0)+"_init", CDD.TRUE, invq );
		q.addTransition( q, CDD.TRUE, new String[0] );
		nonDetInit.add( q );
		for(i=1;i<clocks.size();i++)
		{
			invp=RangeDecision.create( clocks.get(i), RangeDecision.OP_LT, 10 );
			p=new Phase( clocks.get(i)+"_init", CDD.TRUE, invp );
			nonDetInit.add( p );
			//nonDetInit.get(i-1).getTransitions().add( new Transition( nonDetInit.get(i-1), inv, new String[0], nonDetInit.get(i) ) );
			q.addTransition( p, invq, new String[0] );
			p.addTransition( p, CDD.TRUE, new String[0] );
			//phases.add(p);
			q=p;
			invq=invp;
		}
		
		for(i=0;i<init.size();i++)
		{
			nonDetInit.get( nonDetInit.size()-1 ).addTransition( init.get(i), invq, new String[0] );
		}
		
		for(i=0;i<nonDetInit.size();i++)
		{
			phases.add( nonDetInit.get(i) );
		}
		phases.add( catchAll );
		Phase[] ainit=new Phase[1];
		ainit[0]=nonDetInit.get(0);
		PhaseEventAutomata res=new PhaseEventAutomata( pea.getName()+"PEAbs_"+size+"_Set"+num, phases.toArray(new Phase[0]), 
				ainit, clocks );
		
		return res;
	}*/
	
	
	private Vector<String> getClocks( Vector<Phase> phases )
	{
		Vector<String> res=new Vector<String>();
		int i;
		for( i=0;i<phases.size();i++ )
		{
			Vector<String> clocks=getClocksFromCDD( phases.get(i).getClockInvariant() );
			res.addAll(clocks);
		}
		res=unify(res);
		return res;
	}
	
	private Vector<String> getClocks( PhaseEventAutomata pea )
	{
		Vector<String> res=new Vector<String>();
		int i;
		for( i=0;i<pea.getPhases().length;i++ )
		{
			Vector<String> clocks=getClocksFromCDD( pea.getPhases()[i].getClockInvariant() );
			res.addAll(clocks);
		}
		res=unify(res);
		return res;
	}
	
	private Vector<String> unify( Vector<String> vect )
	{
		Vector<String> clocks=(Vector<String>)vect.clone();
		//Collections.sort( clocks );
		Collections.sort(clocks, new Comparator<String>() {
			   public int compare(String s1, String s2){
			      return s1.compareTo(s2);
			   }
			});
		int j=1;
		while( j<clocks.size() )
		{
			if( clocks.get(j).compareTo( clocks.get(j-1) )==0 )
			{
				clocks.remove(j);
			}
			else
				j++;
		}
		return clocks;
	}
	
	private Vector<String> getClocksFromCDD( CDD cdd )
	{
		Vector<String> res=new Vector<String>();
		
		if( cdd==CDD.FALSE || cdd==CDD.TRUE || cdd==null )
			return res;
		
		
		int i;
		if( cdd.getDecision() instanceof RangeDecision )
		{
			RangeDecision r=(RangeDecision)cdd.getDecision();
			res.add(r.getVar());
		}
			
		for( i=0;i<cdd.getChilds().length;i++ )
		{
			res.addAll( getClocksFromCDD( cdd.getChilds()[i] ) );
		}
		
		return res;
	}
	
	
	public int getNum()
	{
		return num;
	}
	
	public void setNum( int num )
	{
		this.num=num;
	}
}
