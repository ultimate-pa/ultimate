package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqCheck.PatternToPEA;


public class srParsePattern {
	
	//contains all CDDs occuring in the pattern in reverse order
	private Vector<CDD> cdds; 
	public Vector<CDD> getCdds() {
		return cdds;
	}

	private int duration;
	
	protected static CDD q_cdd_default = BooleanDecision.create("Q");
	protected static CDD r_cdd_default = BooleanDecision.create("R");
	
	
	public int getDuration() {
		return duration;
	}

	public void setDuration(int duration) {
		this.duration = duration;
	}
	
	private PhaseEventAutomata pea;
	
	public Vector<Integer> getElemHashes()
	{
		int i;
    	final Vector<Integer> res=new Vector<Integer>();
    	
    	for( i=0;i<cdds.size();i++ )
    	{
    		res.addAll( cdds.get(i).getElemHashes() );
    	}
    	
    	if( scope.getCdd1()!=null && scope.getCdd1()!= q_cdd_default && scope.getCdd1()!= r_cdd_default)
		{
			res.addAll( scope.getCdd1().getElemHashes() );
		}
    	
    	if( scope.getCdd2()!=null && scope.getCdd2()!= q_cdd_default && scope.getCdd2()!= r_cdd_default )
		{
			res.addAll( scope.getCdd2().getElemHashes() );
		}
    	
    	return res;
	}
	
	private boolean subExpressionsContained( CDD cdd, Vector<CDD> list )
	{
		if( cdd==null || list==null || cdd==CDD.FALSE || cdd==CDD.TRUE ) {
			return true;
		}
		
		final String var=cdd.getDecision().getVar();
		int i;
		boolean found=false;
		
		for(i=0;i<list.size();i++)
		{
			final String lvar=list.get(i).getDecision().getVar();
			if( lvar.compareTo( var )==0 )
			{
				found=true;
				break;
			}
		}
		if( !found ) {
			return false;
		}
		
		for(i=0;i<cdd.getChilds().length;i++)
		{
			if( !subExpressionsContained( cdd.getChilds()[i], list ) ) {
				return false;
			}
		}
		
		return true;
	}
	
	public void mergeCDDs( Vector<CDD> cdds )
	{
		int i;
		
		if( cdds==null ) {
			return;
		}
		
		if( this.cdds==null ) {
			this.cdds=new Vector<CDD>();
		}
			
		for(i=0;i<cdds.size();i++)
		{
			this.cdds.add(cdds.get(i));
		}
	}
	
	
	public PhaseEventAutomata transformToPea()
	{
		pattern.transform();
		
		return pea;
	}
	
	protected PatternToPEA peaTransformator;
	
	public PatternToPEA getPeaTransformator() {
		return peaTransformator;
	}

	public void setPeaTransformator(PatternToPEA peaTransformator) {
		this.peaTransformator = peaTransformator;
	}


	public abstract class PatternType
	{
		
		public PatternType() {
			super();
		}

		protected CDD getDefaultQ_cdd() {
			return q_cdd_default;
		}

		protected CDD getDefaultR_cdd() {
			return r_cdd_default;
		}
		
		public abstract void transform();
		
		@Override
		public abstract String toString();
	}
	
	public class InvariantPattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0); 
			
			pea = peaTransformator.invariantPattern(p_cdd, q_cdd, r_cdd, s_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" holds as well";
			
			
			return res;
		}
	}
	
	public class InstAbsPattern extends PatternType
	{
		// erwartet cdds rückwärts
		@Override
		public void transform()
		{
			
				//Case: GLOBALLY
				if ( scope instanceof srParseScopeGlob ){
					if (cdds.size() !=1){
						//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
						System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
					}
					
					final CDD p_cdd = cdds.get(0); //für Duration Calculus muß das als CDD gegeben sein
					final CDD q_cdd = getDefaultQ_cdd();
					final CDD r_cdd = getDefaultR_cdd();
					
					
					pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString() );
				}
				//CASE: BEFORE R
				else 
					if (scope instanceof srParseScopeBefore){
						if(cdds.size()!=2){
							//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
							System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
						}
						
						final CDD p_cdd = cdds.get(0); //für Duration Calculus muß das als CDD gegeben sein
						final CDD q_cdd = getDefaultQ_cdd();
						final CDD r_cdd = cdds.get(1); 
						
						
						
						pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
					
				}
				//CASE: AFTER Q UNTIL R
					else 
						if (scope instanceof srParseScopeAfterUntil){
						if (cdds.size() !=1){
							//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
							System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
						}

						final CDD p_cdd = cdds.get(0);
						final CDD q_cdd = scope.getCdd1();
						final CDD r_cdd = scope.getCdd2();

						pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
						
					}
				//CASE: AFTER Q
						else 
							if (scope instanceof srParseScopeAfter){
							if (cdds.size() !=1){
								//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
								System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
							}
							final CDD p_cdd = cdds.get(0); //für Duration Calculus muß das als CDD gegeben sein
							final CDD q_cdd = scope.getCdd1();
							final CDD r_cdd = getDefaultR_cdd();
							
							pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
						}
				//CASE: BETWEEN Q AND R
							else 
								if (scope instanceof srParseScopeBetween){
								if (cdds.size() !=1){
									//Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
									System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
								}
								
								final CDD p_cdd = cdds.get(0); //für Duration Calculus muß das als CDD gegeben sein
								final CDD q_cdd = scope.getCdd1();
								final CDD r_cdd = scope.getCdd2();
								
								pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
								//return this.getFormulaInLTL();
							}
		}	
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is never the case that \""+cdds.get(0)+"\" holds";
			
			return res;
		}
	}
	
	public class UniversalityPattern extends PatternType
	{
		@Override
		public void transform()
		{
			/*
			CDD p_cdd = BooleanDecision.create("ANB_Request_valid = 1");
			CDD q_cdd = BooleanDecision.create("ANB_Teilbremsung_Freigabe = 1").and( BooleanDecision.create("ANB_info_Teilbremsung = 1") ); 
			CDD r_cdd = p_cdd;
			*/
			
			
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
						
			pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that \""+cdds.get(0)+"\" holds";
			
			return res;
		}
	}
	
	public class BndExistencePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			
			pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			res="transitions to states in which \""+cdds.get(0)+"\" holds occur at most twice";
			return res;
		}
	}
	
	public class PrecedencePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0);
			
			pea = peaTransformator.precedencePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" previously held";
			
			return res;
		}
	}
	
	public class PrecedenceChain12Pattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(2); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(1);
			final CDD t_cdd = cdds.get(0);
			
			pea = peaTransformator.precedenceChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(2)+"\" holds and is succeeded by \""+cdds.get(1)+"\", then \""+cdds.get(0)+"\" previously held";
			
			return res;
		}
	}
	
	public class PrecedenceChain21Pattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(2); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(1);
			final CDD t_cdd = cdds.get(0);
			
			pea = peaTransformator.precedenceChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(2)+"\" holds, then \""+cdds.get(1)+"\" previously held and was preceded by \""+cdds.get(0)+"\"";
			
			return res;
		}
	}
	
	public class ResponsePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0);
			
			pea = peaTransformator.responsePattern(p_cdd, q_cdd, r_cdd, s_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" eventually holds";
			
			return res;
		}
	}
	
	
	public class ResponseChain12Pattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(2); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(1);
			final CDD t_cdd = cdds.get(0);
			
			pea = peaTransformator.responseChainPattern12(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(2)+"\" holds, then \""+cdds.get(1)+"\" eventually holds and is succeeded by \""+cdds.get(0)+"\"";
			
			return res;
		}
	}
	
	public class ResponseChain21Pattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(2); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(1);
			final CDD t_cdd = cdds.get(0);
			
			pea = peaTransformator.responseChainPattern21(p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(3)+"\" holds and is succeeded by \""+cdds.get(2)+"\", then \""+cdds.get(1)+"\" eventually holds after \""+cdds.get(0)+"\"";
			
			return res;
		}
	}
	
	public class ConstrainedChainPattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			
			System.err.println( "Kein PEA" );
			
			pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(5)+"\" holds, then \""+cdds.get(4)+"\" eventually holds and is succeeded by \""+cdds.get(3)+"\", where \""+cdds.get(2)+"\" does not hold between \""+cdds.get(1)+"\" and \""+cdds.get(0)+"\"";
			
			return res;
		}
	}
	
	
	public class MinDurationPattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			
			pea = peaTransformator.minDurationPattern(p_cdd, q_cdd, r_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that once \""+cdds.get(0)+"\" becomes satisfied, it holds for at least \""+duration+"\" time units";
			
			return res;
		}
	}
	
	public class MaxDurationPattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			
			pea = peaTransformator.maxDurationPattern(p_cdd, q_cdd, r_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that once \""+cdds.get(0)+"\" becomes satisfied, it holds for less than \""+duration+"\" time units";
			
			return res;
		}
	}
	
	
	public class BndReccurrencePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(0); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			
			pea = peaTransformator.periodicPattern(p_cdd, q_cdd, r_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that \""+cdds.get(0)+"\" holds at least every \""+duration+"\" time units";
			
			return res;
		}
	}
	
	
	public class BndResponsePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0);
			
			pea = peaTransformator.bndResponsePattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" holds after at most \""+duration+"\" time units";
			
			return res;
		}
	}
	
	
	public class BndInvariancePattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0);
			
			pea = peaTransformator.bndInvariancePattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that if \""+cdds.get(1)+"\" holds, then \""+cdds.get(0)+"\" holds for at least \""+duration+"\" time units";
			
			return res;
		}
	}
	
	public class PossibilityPattern extends PatternType
	{
		@Override
		public void transform()
		{
			
			System.err.println( "Kein PEA" );
			
			pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="if \""+cdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+cdds.get(0)+"\" eventually holds";
			
			return res;
		}
	}
	
	public class BndPossResponsePattern extends PatternType
	{
		@Override
		public void transform()
		{
			System.err.println( "Kein PEA" );
			
			pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="if \""+cdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+cdds.get(0)+"\" holds after at most \""+duration+"\" time units";
			
			return res;
		}
	}
	
	public class BndPossInvariancePattern extends PatternType
	{
		@Override
		public void transform()
		{
			System.err.println( "Kein PEA" );
			
			pea = null;//peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="if \""+cdds.get(1)+"\" holds, then there is at least one execution sequence such that \""+cdds.get(0)+"\" holds for at least \""+duration+"\" time units";
			
			return res;
		}
	}
	
	public class BndEntryConditionPattern extends PatternType
	{
		@Override
		public void transform()
		{
			final CDD p_cdd = cdds.get(1); 
			final CDD q_cdd = scope.getCdd1(); 
			final CDD r_cdd = scope.getCdd2();
			final CDD s_cdd = cdds.get(0);
			
			pea = peaTransformator.bndEntryConditionPattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
		}
		
		@Override
		public String toString()
		{
			String res=new String();
			
			res="it is always the case that after \""
			    + cdds.get(1) + "\" holds for \""+duration + 
			    "\" time units, then \"" + cdds.get(0) + "\" holds";
			
			return res;
		}
	}
	
	
	
	// zur weitergabe der CDDs im Parser notwendig - oder auch nicht
	/*public class InvalidPattern extends PatternType
	{
	}*/
	
	private srParseScope scope;
	private PatternType pattern;
	
	public PatternType getPattern() {
		return pattern;
	}

	public void setPattern(PatternType pattern) {
		this.pattern = pattern;
	}

	public srParseScope getScope() {
		return scope;
	}

	public void setScope(srParseScope scope) 
	{
		this.scope = scope;
	}		

	public srParsePattern()
	{
		scope=null;
		pattern=null;
	}
	
	public srParsePattern(  srParseScope scope )
	{
		setScope( scope );
		pattern=null;
	}
	
	public srParsePattern(  srParseScope scope, PatternType pattern )
	{
		setScope( scope );
		this.pattern=pattern;
	}
	
	@Override
	public String toString()
	{
		String res=new String();
		
		res=scope.toString()+pattern.toString();
		
		return res;
	}

}
