package caseStudies;

import java.io.IOException;
import java.util.Vector;
import java.io.*;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.RangeDecision;
import pea.Transition;
import pea.modelchecking.DOTWriter;
import pea.modelchecking.J2UPPAALConverter;
import pea.reqCheck.TransformPEAStateNames;
import PatternLanguage.PL_Pattern2Logic;
import PatternLanguage.PL_initiatedPattern;
import PatternLanguage.Requirement;
import java.util.List;
import java.util.Iterator;

public class SimpleDlFind {

	
	public class FoundEntry
	{
		private Phase phase;

		public Phase getPhase() {
			return phase;
		}

		public void setPhase(Phase phase) {
			this.phase = phase;
		}
		
		private boolean mayDeadlock;

		public boolean isMayDeadlock() {
			return mayDeadlock;
		}

		public void setMayDeadlock(boolean mayDeadlock) {
			this.mayDeadlock = mayDeadlock;
		}
		
		public FoundEntry( Phase phase, boolean mayDl )
		{
			this.phase=phase;
			mayDeadlock=mayDl;
		}
		
		public String toString()
		{
			String res;
			if( mayDeadlock )
				res="possible Deadlock in location " + phase;
			else
				res="Deadlock in location " + phase;
			
			return res;
		}
	}
	
	private boolean hasEqDecision( CDD cdd )
	{
		/*
		if( cdd.getDecision() instanceof RangeDecision )
		{
			RangeDecision rd=(RangeDecision)cdd.getDecision();
			if (rd.getLimits()[childs - 1] / 2 == rd.getLimits()[childs] / 2)
	            return true;
		}*/
		String c=cdd.toString();
		if( c.indexOf( "==" )>=0 )
			return true;
		return false;
	}
	
	CDD tguard;
	
	
	/*private int decide( Phase phase, Transition trans ) // 2010-07-26  liefert gute ergebnisse
	{
		CDD guard=trans.getGuard();
		CDD ci=phase.getClockInvariant();
		CDD destci=trans.getDest().getClockInvariant();
		//CDD destci=trans.getDest().getClockInvariant().and(guard);
		
		CDD neg=guard.negate().and( destci );
		CDD res=ci.and(neg);
		
		//if( ( guard.getChilds()!=null && !guard.equals(ci) && guard.implies(ci) ) || hasEqDecision( res ) ) // 2010-07-25
		if( ( guard.getChilds()!=null && !guard.equals(ci) && guard.implies(ci) ) || hasEqDecision( res ) )
		{
			//phase.isDlSuspect=true;
			return 1;
		}
		else
		{
			CDD t=ci.and( guard.and( trans.getDest().getClockInvariant() ) );
			if( hasEqDecision( t ) )
			{
				//phase.isDlSuspect=true;
				return 2;
			}
		}
		
		return 0;
	}*/
	
	private int decide( Phase phase, Transition trans )
	{
		CDD guard=trans.getGuard();
		CDD ci=phase.getClockInvariant();
		CDD destci=trans.getDest().getClockInvariant();
		
		CDD neg=guard.negate().and( destci );
		CDD res=ci.and(neg);
		
		//if( ( guard.getChilds()!=null && !guard.equals(ci) && guard.implies(ci) ) || hasEqDecision( res ) ) // 2010-07-25
		if( ( guard.getChilds()!=null && !guard.equals(ci) && guard.implies(ci) ) || hasEqDecision( res ) )
		{
			//phase.isDlSuspect=true;
			return 1;
		}
		else
		{
			CDD t=ci.and( guard.and( trans.getDest().getClockInvariant() ) );
			if( hasEqDecision( t ) )
			{
				//phase.isDlSuspect=true;
				return 2;
			}
		}
		
		return 0;
	}
	
	private int decide2( Phase phase, Transition trans )
	{
		return 0;
	}
	
	// true wenn cdd eine clock enthält, sonst false
	private boolean hasClockConstraint(CDD cdd)
	{
		if( cdd==CDD.TRUE || cdd==CDD.FALSE )
			return false;
		
		if( cdd.getDecision() instanceof RangeDecision )
			return true;
		
		for(int i=0;i<cdd.getChilds().length;i++)
		{
			if( hasClockConstraint( cdd.getChilds()[i] ) )
				return true;
		}
		
		return false;
	}
	
	private boolean strInArr(String s, String[] arr)
	{
		for(int i=0;i<arr.length;i++ )
		{
			if( arr[i].compareTo(s)==0 )
				return true;
		}
		
		return false;
		
	}
	
	private boolean hasClockConstraintWithoutReset(CDD cdd, String[] reset)
	{
		if( cdd==CDD.TRUE || cdd==CDD.FALSE )
			return false;
		
		if( cdd.getDecision() instanceof RangeDecision )
		{
			RangeDecision rd=(RangeDecision)cdd.getDecision();
			if( !strInArr( rd.getVar(), reset ) )
				return false;
		}
		
		for(int i=0;i<cdd.getChilds().length;i++)
		{
			if( hasClockConstraintWithoutReset( cdd.getChilds()[i], reset ) )
				return true;
		}
		
		return false;
	}
	
	private int inspectPhase2( Phase phase )
	{
		int pc=0;
		int prob=0;
		
		if( phase.getClockInvariant()==CDD.TRUE )
		{
			return 0;
		}
		
		List<Transition> trans=phase.getTransitions();
		Iterator it=trans.iterator();
		tguard=phase.getClockInvariant().negate();
		CDD cdd=phase.getClockInvariant();
		
		while(it.hasNext())
		{
			Transition t= (Transition)it.next();
			if( !hasClockConstraint( t.getGuard() ) )
			{
				return 0;
				//pc=-1;
				//break;
			}
			if( !hasClockConstraintWithoutReset( t.getDest().getClockInvariant(), t.getResets() ) )
				return 0;
			
			cdd=cdd.and( t.getGuard().negate().and( t.getDest().getClockInvariant().negate() ) );
			
			
		}
		
		//if( pc<0 )
			//return 0;
		return 0;
	}
	
	private int inspectPhase( Phase phase )
	{
		int pc=0;
		int prob=0;
		List<Transition> trans=phase.getTransitions();
		Iterator it=trans.iterator();
		tguard=phase.getClockInvariant().negate();
		
		while(it.hasNext())
		{
			Transition t= (Transition)it.next();
			tguard=tguard.and( t.getGuard().negate().and( t.getDest().getClockInvariant().negate() ) );
			
			//if( tguard==CDD.FALSE )
				//break;
			
			if( /*( t.getType()==Transition.NORMAL ) &&*/ ( t.getDest()!=phase ) )
			{
				int res=decide( phase, t);
				if( res!=0 )
				{
					pc++;
					prob+=res;
				}
			}
			else
			{
				pc++;
				prob++;
			}
			
		}
		
		//if( tguard==CDD.FALSE )
			//return 1;
		
		if( pc==trans.size() )
		{
			//phase.isDlSuspect=true;
			if( prob==pc )
				return 1;
			else
				if( tguard==CDD.FALSE )
					return 0;
				else
					return 2;
		}
		else
			return 0;
	}
	
	public Vector<SimpleDlFind.FoundEntry> doDlFind( PhaseEventAutomata pea)
	{
		int i;
		Phase []phases=pea.getPhases();
		Vector<SimpleDlFind.FoundEntry> res=new Vector<SimpleDlFind.FoundEntry>();
		
		for( i=0;i<phases.length;i++ )
		{
			int r=inspectPhase( phases[i] );
			if( r!=0 )
			{
				phases[i].isDlSuspect=true;
				res.add( new SimpleDlFind.FoundEntry( phases[i], r==2 ) );
			}
		}
		
		return res;
	}
}
