package caseStudies;

import pea.*;
import java.util.*;

public class PEAbs {


	Vector<Phase> kernel;
	Vector<Phase> init;
	Vector<Phase> entry;
	Vector<Phase> exit;
	Phase[] phases;
	
	
	public PhaseEventAutomata reduce( PhaseEventAutomata pea, String[] clockName )
	{
		getSets( pea, clockName );
		Vector<Phase> phases=new Vector<Phase>();
		//phases.addAll( pea.getPhases() );
		int i=0;
		int kernels=0;
		int entries=0;
		int exits=0;
		int removed=0;
		int diffs=0;
		for(i=0;i<pea.getPhases().length;i++ )
		{
			if( pea.getPhases()[i].isKernel || pea.getPhases()[i].isEntry || pea.getPhases()[i].isExit )
			{
				phases.add( pea.getPhases()[i] );
				
				if( pea.getPhases()[i].isKernel )
					kernels++;
				
				if( pea.getPhases()[i].isEntry )
					entries++;
				
				if( pea.getPhases()[i].isExit )
					exits++;
				
				if( pea.getPhases()[i].isExit && !pea.getPhases()[i].isEntry )
					diffs++;
			}
			else
				removed++;

		}
		
		/*while( i<phases.size() )
		{
			if( !phases.get(i).isKernel && !phases.get(i).isEntry && phases.get(i).isExit )
			{
				phases.removeElementAt(i);
			}
			else
			{
				int j=0;
				while( j<phases.get(i).getTransitions().size() )
				{
					Phase dest=phases.get(i).getTransitions().get(i).getDest();
					if( !dest.isKernel && !dest.isEntry && dest.isExit )
					{
						
					}
					else
						j++;
				}
				i++;
			}
		}*/
		
		System.out.println( "PEAbs: Reduced pea has "+kernels+" kernels, "+entries+ " entry- , "+exits+" exitset element, "+removed+" removed, "+diffs+" diffs" );
		
		PhaseEventAutomata res=new PhaseEventAutomata( pea.getName()+"PEAbs", phases.toArray(new Phase[0]), 
				init.toArray(new Phase[0]), pea.getClocks() );
		
		
		return res;
	}
	
	private void getSets(PhaseEventAutomata pea, String[] clockName)
	{
		kernel=new Vector<Phase>();
		init=new Vector<Phase>();
		entry=new Vector<Phase>();
		exit=new Vector<Phase>();
		phases=pea.getPhases();
		
		Phase phase;
		int i;
		
		getEntryExitKern( clockName );
		
		phase=pea.getInit()[0];
		getInit( phase );
		for( i=1;i<pea.getInit().length;i++ )
		{
			for(int j=0;j<phases.length;j++)
			{
				phases[j].isVisited=false;
			}
			
			phase=pea.getInit()[i];
			getInit( phase );	
		}
	}
	
	/*private void getEntryExitKern( PhaseWrapper phase, String clockName, boolean predIsKernel  )
	{
		if( clockInCdd( phase.phase.getClockInvariant(), clockName ) )
		{
			phase.isKernel=true;
			kernel.add( phase );
		}
		
		for( int i=0;i<phase.phase.getTransitions().size();i++ )
		{
			getEntryExitKern( phase.phase.getTransitions().get(i), clockName, phase.isKernel );
		}
	}*/
	
	private void getEntryExitKern( String[] clockName )
	{
		int i;
		for(i=0;i<phases.length;i++)
		{
			phases[i].isKernel=false;
			phases[i].isInit=false;
			phases[i].isEntry=false;
			phases[i].isExit=false;
			phases[i].isVisited=false;
			
			if( clockInCdd( phases[i].getClockInvariant(), clockName) )
			{
				phases[i].isKernel=true;
				kernel.add( phases[i] );
			}
			else
				phases[i].isKernel=false;
		}
		
		for(i=0;i<phases.length;i++)
		{
			if( !phases[i].isKernel )
			{
				int j;
				for(j=0;j<phases[i].getTransitions().size();j++ )
				{
					if( phases[i].getTransitions().get(j).getDest().isKernel )
					{
						phases[i].isEntry=true;
						entry.add( phases[i] );
					}
				}
			}
			else
			{
				int j;
				for(j=0;j<phases[i].getTransitions().size();j++ )
				{
					if( !phases[i].getTransitions().get(j).getDest().isKernel && 
							!phases[i].getTransitions().get(j).getDest().isExit )
					{
						phases[i].getTransitions().get(j).getDest().isExit=true;
						entry.add( phases[i].getTransitions().get(j).getDest() );
					}
				}
			}
		}
	}
	
	private void getInit( Phase phase )
	{
		if( !phase.isVisited )
		{
			phase.isVisited=true;
			if( !phase.isEntry )
			{
				int j;
				for(j=0;j<phase.getTransitions().size();j++ )
				{
						getInit( phase.getTransitions().get(j).getDest() );
				}
			}
			else
			{
				if( !phase.isInit )
				{
					phase.isInit=true;
					init.add( phase );
				}
			}
		}
	}
	
	private boolean clockInCdd( CDD cdd, String[] clockName )
	{
		String str=cdd.toString();
		for(int i=0;i<clockName.length;i++ )
		{
			if( !str.matches( "(.*)"+clockName[i]+"[^a-zA-Z_0-9](.*)" ) )
				return false;
		}
		return true;
	}
	
	
	
	
	
	public PhaseEventAutomata stateReduce( PhaseEventAutomata pea, Phase[] locations, int envsize )
	{
		Vector<Phase> phases=new Vector<Phase>();
		Vector<Phase> init=new Vector<Phase>();
		
		int n;
		for( n=0;n<envsize;n++ )
		{
			int i;
			for( i=0;i<pea.getPhases().length;i++ )
			{
				if( pea.getPhases()[i].flags>0 )
					continue;
				
				int j;
				for( j=0;j<locations.length;j++ )
				{
					if( pea.getPhases()[i].equals(locations[j]) )
					{
						locations[j].flags= 1;
						//locations[j].setName( "cand" );
						phases.add( pea.getPhases()[i] );
					}
					else
					{
						int ii;
						for(ii=0;ii<pea.getPhases()[i].getTransitions().size();ii++ )
						{
							if( pea.getPhases()[i].getTransitions().get(ii).getDest().flags>0 &&
									pea.getPhases()[i].getTransitions().get(ii).getDest().flags<=envsize )
							{
								pea.getPhases()[i].flags=pea.getPhases()[i].getTransitions().get(ii).getDest().flags+1;
								phases.add( pea.getPhases()[i] );
							}
						}
					}
				}
			}
		}
		
	
		System.out.println( "Reduced Automata has "+phases.size()+" locations." );
		
		Vector<String> clocks=getClocks(pea);	
		int i;
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
		
		for( n=0;n<phases.size();n++ )
		{
			i=0;
			CDD g=CDD.FALSE;
			while(i<phases.get(n).getTransitions().size()) // unnötige transitionen entfernen
			{
				if( phases.get(n).getTransitions().get(i).getDest().flags==0 )
				{
					g=phases.get(n).getTransitions().get(i).getGuard().or(g);
					phases.get(n).getTransitions().remove(i);
				}
				else
					i++;
			}
		}
		
		for(n=0;n<pea.getInit().length;n++)
		{
			pea.getInit()[n].isInit=true;
			init.add( pea.getInit()[n] );
		}
		
		for(i=0;i<pea.getPhases().length;i++ )
		{
			for(int j=0;j<pea.getPhases()[i].getTransitions().size();j++)
			{
				if( pea.getPhases()[i].flags==0 && pea.getPhases()[i].getTransitions().get(j).getDest().flags!=0 )
				{
					pea.getPhases()[i].getTransitions().get(j).getDest().isEntry=true;
					init.add( pea.getPhases()[i].getTransitions().get(j).getDest() );
				}
			}
		}
		
		for(i=0;i<init.size();i++)
		{
			//nonDetInit.get( nonDetInit.size()-1 ).getTransitions().add( new Transition( nonDetInit.get(nonDetInit.size()-1), inv, new String[0], init.get(i) ) );
			if( ( init.get(i).isInit || init.get(i).isEntry ) && init.get(i).flags>0 )
				nonDetInit.get( nonDetInit.size()-1 ).addTransition( init.get(i), invq, new String[0] );
		}
		
		for(i=0;i<nonDetInit.size();i++)
		{
			phases.add( nonDetInit.get(i) );
		}
		
		Phase[] ainit=new Phase[1];
		ainit[0]=nonDetInit.get(0);
		PhaseEventAutomata res=new PhaseEventAutomata( pea.getName()+"PEAbs_"+envsize+"_Env", phases.toArray(new Phase[0]), 
				ainit, clocks );
		
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
}






