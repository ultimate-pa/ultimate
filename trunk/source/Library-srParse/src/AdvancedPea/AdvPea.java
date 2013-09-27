package AdvancedPea;

import java.util.List;

import pea.*;

import java.util.*;

public class AdvPea {
	
	PhaseEventAutomata pea;
	
	public PhaseEventAutomata getPea() {
		return pea;
	}

	int bitsize=0;
	
	int[] transCnt; // anzahl der von Location i ausgehenden Transitionen mit guard != false
	
	
	public int[] getTransCnt() {
		return transCnt;
	}

	public int getBitsize() {
		return bitsize;
	}

	int[] initial;
	public int[] getInitial() {
		return initial;
	}

	String name;
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	String[] stateNames;
	public String[] getStateNames() {
		return stateNames;
	}

	CDD[] stateInvs;
	public CDD[] getStateInvs() {
		return stateInvs;
	}

	CDD[] clockInvs;
	public CDD[] getClockInvs() {
		return clockInvs;
	}

	CDD[][] guards;
	public CDD[][] getGuards() {
		return guards;
	}

	String[] clocks;
	Vector<CDD> disjuncts;
	//CDD commonExp=null;
	int[] timed;
	
	public int[] getTimed() {
		return timed;
	}

	int[][] active;
	public int[] getActive(int idx ) {
		if( active!=null && idx<active.length )
			return active[idx];
		else
			return null;
	}

	public void setActive(int idx, int[] active) {
		this.active[idx] = active;
	}

	public int[] getWaiting(int idx ) {
		return waiting[idx];
	}

	public void setWaiting(int idx, int[] waiting) {
		this.waiting[idx] = waiting;
	}

	public int[] getExact(int idx ) {
		return exact[idx];
	}

	public void setExact(int idx, int[] exact) {
		this.exact[idx] = exact;
	}

	int[][] waiting;
	int[][] exact;

	public static int indexOf( Phase[] phases, Phase p )
	{
		int i;
		for(i=0;i<phases.length;i++)
		{
			if( phases[i]==p )
			{
				return i;
			}
		}
		
		return -1;
	}
	
	public AdvPea( PhaseEventAutomata pea )
	{
		this.pea=pea;
		name=pea.getName();
		int len=pea.getPhases().length;
		stateInvs=new CDD[len];
		clockInvs=new CDD[len];
		
		bitsize=(int)Math.ceil( Math.log( (double)len )/Math.log(2.0) );
		
		//int alen=0;
		//for(int i=0;i<len;i++)
			//alen+=pea.getPhases()[i].getBitsAct().length;
		
		active=new int[len][];
		waiting=new int[len][];
		exact=new int[len][];
		guards=new CDD[len][len];
		stateNames=new String[len];
		clocks=pea.getClocks().toArray( new String[0]);
		int i,j;
		timed=new int[len];
		initial=new int[ pea.getInit().length ];
		int tc=0;
		
		for(i=0;i<len;i++)
		{
			for(j=0;j<len;j++)
				guards[i][j]=CDD.FALSE;
			Phase p=pea.getPhases()[i];
			stateNames[i]=p.getName();
			clockInvs[i]=p.getClockInvariant();
			stateInvs[i]=p.getStateInvariant();
		//	transCnt[i]=p.getTransitions().size();
			
			if( p.getBitsAct()!=null && p.getBitsWait()!=null && p.getBitsExa()!=null )
			{
				active[i]=new int[p.getBitsAct().length];
				waiting[i]=new int[p.getBitsAct().length];
				exact[i]=new int[p.getBitsAct().length];
				for(j=0;j<p.getBitsAct().length;j++)
				{
					active[i][j]=p.getBitsAct()[j];
					waiting[i][j]=p.getBitsWait()[j];
					exact[i][j]=p.getBitsExa()[j];
				}
			}
			
			if( p.getClockInvariant()!=CDD.TRUE )
			{
				timed[tc++]=i;
			}
			
			for(j=0;j<p.getTransitions().size();j++)
			{
				int k=indexOf( pea.getPhases(), p.getTransitions().get(j).getDest() );
				guards[i][k]=p.getTransitions().get(j).getGuard().unprime();
			}
		}
		
		if( tc<len )
		{
			int[] tmp=timed;
			timed=new int[tc];
			System.arraycopy( tmp, 0, timed, 0, tc );
		}
		
		j=0;
		for(i=0;i<pea.getInit().length;i++)
		{
			int idx=indexOf( pea.getPhases(), pea.getInit()[i] );
			if( idx>=0 )
			{
				initial[j++]=idx;
			}
		}
	}
	
	public boolean isTimed()
	{
		return clocks!=null && clocks.length>0;
	}

	
	public CDD[] getDisjuncts(CDD cdd) {
		disjuncts.clear();
        this.cddToDNF(null, cdd);
        int disjunctCount = this.disjuncts.size();
        CDD[] cdds = new CDD[disjunctCount];
        for(int i=0; i<disjunctCount; i++) {
            cdds[i] = (CDD) this.disjuncts.elementAt(i);
        }
        
        return cdds;
    }
	
    private void cddToDNF(CDD buf, CDD cdd) {
        if(cdd == CDD.TRUE) {

        	if( buf==null )
        		buf=CDD.TRUE;
        		
        	this.disjuncts.add(buf);
            return;
        } else if (cdd == CDD.FALSE) {
            return;
        }
        for(int i=0;i<cdd.getChilds().length;i++) {
        	CDD newbuf=buf;
        	if( cdd.getDecision() instanceof RangeDecision )
            {
            	
            	RangeDecision dec=(RangeDecision)cdd.getDecision();
            	
            	int op=cdd.getOp();
            	int val=cdd.getValue();
            	if( op!=RangeDecision.OP_INVALID && val >= 0 )
            	{
	            	if( buf==null )
	            		newbuf=RangeDecision.create( dec.getVar(), op, val );
	            	else
	            		newbuf=buf.and( RangeDecision.create( dec.getVar(), op, val ) );
            	}
            }
            
            this.cddToDNF(newbuf,cdd.getChilds()[i]);
        }
    }
    
    public CDD[] getUntimedDisjuncts(CDD cdd) {
		if( disjuncts==null )
		{
			disjuncts=new Vector<CDD>();
		}
    	
    	disjuncts.clear();
        this.cddToUntimedDNF(null, cdd);
        int disjunctCount = this.disjuncts.size();
        CDD[] cdds = new CDD[disjunctCount];
        for(int i=0; i<disjunctCount; i++) {
            cdds[i] = (CDD) this.disjuncts.elementAt(i);
        }
        
        return cdds;
    }
	
    private void cddToUntimedDNF(CDD buf, CDD cdd) {
        if(cdd == CDD.TRUE) {

        	if( buf==null )
        		buf=CDD.TRUE;
        		
        	this.disjuncts.add(buf);
            return;
        } else if (cdd == CDD.FALSE) {
            return;
        }
        else if( cdd.getDecision() instanceof RangeDecision )
        {
        	return; // wir sind nur an zeitunabhängigen konjunktionen interessiert 
        }
        	
        for(int i=0;i<cdd.getChilds().length;i++) {
        	
        	if (cdd.getChilds()[i] == CDD.FALSE)
                continue;
        	
        	CDD newbuf=buf;
        	if( cdd.getDecision() instanceof BooleanDecision )
            {
            	BooleanDecision dec=(BooleanDecision)cdd.getDecision();
            	
            	CDD t=BooleanDecision.create( dec.getVar() );
            	if( i==1 )
            		t=t.negate();
            	
            	if( buf==null )
            		newbuf=t;
            	else
            		newbuf=buf.and( t );
            }
        	
            
            this.cddToDNF(newbuf,cdd.getChilds()[i]);
        }
    }
    
    public int getPhaseCount()
    {
    	return stateInvs.length;
    }
    
    
    /*
     * Wendet eine stateInvariante explizit auf alle StateInvarinaten an und entfernt 
     * states mit unerfüllbaren stateinvarianten
     */
    public void applyInvariant( CDD inv )
    {
    	int i,j, del, offs;
    	
    	i=0;
    	j=0;
    	del=0;
    	offs=0;
    	for(i=0;i<stateInvs.length-1;i++)
    	{
    		stateInvs[i]=inv.and(stateInvs[i]);
    		if( stateInvs[i]==CDD.FALSE)
    			del++;
    	}
    	
    	if( j==0 )
    		return;
    	
    	
    	CDD[] oldClockInvs=clockInvs;
    	CDD[] oldStateInvs=stateInvs;
    	CDD[][] oldGuards=guards;
    	String[] oldStateN=stateNames;
    	
    	clockInvs=new CDD[clockInvs.length-del];
    	stateInvs=new CDD[stateInvs.length-del];
    	guards=new CDD[guards.length-del][guards.length-del];
    	stateNames=new String[stateNames.length-del];
    	
    	for( i=0;i<oldClockInvs.length;i++ )
    	{
    		if( oldStateInvs[i]==CDD.FALSE )
    		{
    			offs++;
    		}
    		else
    		{
    			clockInvs[i-offs]=oldClockInvs[i];
    			stateInvs[i-offs]=oldStateInvs[i];
    			stateNames[i-offs]=oldStateN[i];
    		
	    		for(j=0;j<oldGuards.length;j++)
	    		{
	    			int of=0;
	    			
	    			if( oldStateInvs[j]==CDD.FALSE )
	        		{
	        			of++;
	        		}
	        		else
	        		{
	        			guards[i-offs][j-of]=oldGuards[i][j];
	        		}
	    		}
    		}
    	}
    }
    
    /*
     * wendet eine stateinvariante auf implizit auf alle stateinvarianten an- 
     * es werden alle konjunktiv verknüpften stateinvarinaten auf erfüllbarkeit geprüft, 
     * locations mti nicht erfüllbaren werden gelöscht, die neue Invariante wird aber nicht 
     * teil der eingenlichen stateinvariante, somit muss weniger berechnet werden, wenn mit den 
     * stateinvarianten gearbeitet wird 
     */
    public void applyInvariantImplicit( CDD inv )
    {
    	int i,j, del, offs;
    	
    	i=0;
    	j=0;
    	del=0;
    	offs=0;
    	for(i=0;i<stateInvs.length-1;i++)
    	{
    		CDD t=inv.and(stateInvs[i]);
    		if( t==CDD.FALSE)
    		{
    			del++;
    			stateInvs[i]=CDD.FALSE;
    		}
    	}
    	
    	if( j==0 )
    		return;
    	
    	
    	CDD[] oldClockInvs=clockInvs;
    	CDD[] oldStateInvs=stateInvs;
    	CDD[][] oldGuards=guards;
    	String[] oldStateN=stateNames;
    	
    	clockInvs=new CDD[clockInvs.length-del];
    	stateInvs=new CDD[stateInvs.length-del];
    	guards=new CDD[guards.length-del][guards.length-del];
    	stateNames=new String[stateNames.length-del];
    	
    	for( i=0;i<oldClockInvs.length;i++ )
    	{
    		if( oldStateInvs[i]==CDD.FALSE )
    		{
    			offs++;
    		}
    		else
    		{
    			clockInvs[i-offs]=oldClockInvs[i];
    			stateInvs[i-offs]=oldStateInvs[i];
    			stateNames[i-offs]=oldStateN[i];
    		
	    		for(j=0;j<oldGuards.length;j++)
	    		{
	    			int of=0;
	    			
	    			if( oldStateInvs[j]==CDD.FALSE )
	        		{
	        			of++;
	        		}
	        		else
	        		{
	        			guards[i-offs][j-of]=oldGuards[i][j];
	        		}
	    		}
    		}
    	}
    }
    
    /*
     * wenn this ein Invarianten Pea ist ( hat nur eine Phase) und b auch werden die 
     * Invarianten und die guards beider pea konjunktiv verbunden und in this gespeichert
     */
    public boolean inv_merge( AdvPea b )
    {
    	if( getPhaseCount()!=1 || b.getPhaseCount()!=1 )
    	{
    		return false;
    	}
    	
    	clockInvs[0]=clockInvs[0].and( b.clockInvs[0] );
    	if( b.clocks.length>0 )
    	{
    		String [] clocks_old=clocks;
    		clocks=new String[ clocks_old.length+b.clocks.length ];
    		System.arraycopy( clocks, 0, clocks_old, 0, clocks_old.length );
    		System.arraycopy( clocks, clocks_old.length, b.clocks, 0, b.clocks.length );
    	}
    	
    	
    	guards[0][0]=guards[0][0].and( b.guards[0][0] );
    	name=name+"_C_"+b.name;
    	stateInvs[0]=stateInvs[0].and( b.stateInvs[0] );
    	
    	if( timed.length==0 && b.timed.length>0 )
    	{
    		timed=new int[1];
    		timed[0]=0;
    	}
    	
    	
    	return true;
    }
}










