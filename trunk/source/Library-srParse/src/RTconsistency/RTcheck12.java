package RTconsistency;


import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.Stack;
import java.util.Random;

import pea.*;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck6.GI;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.lang.Math;


/*
 * randomwalk auf explizitem PEA
 * generiert Pfade in smtlib2 format für Z3
 * 
 *  komplett randomisiertes DBMC
 *  wird für "kompositionale abstraktionsheuristik" für DBMC benötigt
 */
public class RTcheck12 {
	Stack<Phase> st;
	int maxlength=100;
	public int getMaxlength() {
		return maxlength;
	}

	public void setMaxlength(int maxlength) {
		this.maxlength = maxlength;
	}

	public int getMaxloopunroll() {
		return maxloopunroll;
	}

	public void setMaxloopunroll(int maxloopunroll) {
		this.maxloopunroll = maxloopunroll;
	}


	int maxloopunroll;
	Random rand;
	String phaseName;
	
	static int FL_ON_STACK=1;
	static int FL_VISITED=2;
	
	public RTcheck12()
	{
		st=new Stack<Phase>();
		rand=new Random();
	}
	
	public void setSeed( long seed )
	{
		rand.setSeed( seed );
	}
	
	
	
	public String getPhaseName() {
		return phaseName;
	}

	public void setPhaseName(String phaseName) {
		this.phaseName = phaseName;
	}


	public void check( PhaseEventAutomata pea )
	{
		try{
			//for( int i=0;i<50;i++ )
			{
				st.clear();
				docheck( pea );
			}
		}catch(Exception e)
		{
			e.printStackTrace();
		}
	}
	
	private void docheck(PhaseEventAutomata pea )
	{
		try{
			
			// flags aller phasen zurücksetzen
			for( int i=0;i<pea.getPhases().length;i++ )
			{
				pea.getPhases()[i].flags=0;
			}
			
			
			int n=Math.abs( rand.nextInt() ) % pea.getInit().length;
			st.push( pea.getInit()[n] );
			st.peek().flags=FL_ON_STACK | FL_VISITED;
			int ml=Math.min( Math.abs( rand.nextInt() ), 1000 );
			//for( int i=0;i<maxlength;i++ )
			while( true )
			{
				Phase p=st.peek();
				
				// p untersuchen
				
				//if( p.getName().compareTo( phaseName )==0 )
				if( p.dlCheck!=CDD.FALSE && st.size()>=ml /*&& rand.nextInt()>0*/ ) 
				{
					smtFile.write( "(push)\r\n" );
					printHeader( pea, st.size()-1 );
					printStack( pea );
					smtFile.write( "(check-sat)(model)(pop)\r\n" );
					break;
				}
				
				// nächsten knoten suchen
				
				n=Math.abs( rand.nextInt() ) % ( p.getTransitions().size() );
				int k=n;
				Phase dest=p.getTransitions().get(n).getDest();
				while( dest==p /*|| ( dest.flags&FL_VISITED ) != 0*/ )
				{
					n=(n+1)%( p.getTransitions().size() );
					if( n==k )
					{
						st.pop();
						p.flags^=FL_ON_STACK;
						p=st.peek();
						n=Math.abs( rand.nextInt() ) % ( p.getTransitions().size() );
						k=n;
					}
					dest=p.getTransitions().get(n).getDest();
				}
				
				// nächster knoten wurde gefunden
				st.push( dest );
				p.flags|=FL_ON_STACK|FL_VISITED;
			}
			
		//	smtFile.write( "(check-sat)" );
		//	smtFile.write( "(model)(pop)" );
			smtFile.flush();
		}
		catch( Exception e )
		{
			e.printStackTrace();
		}
		
		
	}
	
	
	BufferedWriter smtFile=null;
    
    public void setSmtFile(String filename)
    {
    	try {
			//messageFile=new BufferedWriter(new FileWriter(filename,"UTF8"));
    		smtFile = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename), "UTF8")); 
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	
    }
    
    private void printHeader( PhaseEventAutomata pea, int maxlength)
    {
    	try{
			smtFile.write( "(set-logic QF_RDL)\r\n\r\n" );
			//(declare-funs ((c1_0 Real) (c2_0 Real) (c3_0 Real) (c4_0 Real) (T_0 Real)))
			StringBuffer sb=new StringBuffer();
			for( int k=0;k<=maxlength;k++)
			{
				
				sb.append( "(declare-funs (" );
				for( int i=0;i<pea.getClocks().size();i++ )
				{
					sb.append( "("+pea.getClocks().get(i)+"_"+k +" Real)" );
				}
				sb.append( "(T_"+k+" Real) ))\r\n" );
				smtFile.write( sb.toString() );
				sb=new StringBuffer();
			}
			//StringBuffer sb=new StringBuffer();
			sb.append( "(assert (> T_0 0.0) )" );
			for( int i=1;i<=maxlength;i++ )
			{
				sb.append( "(assert (>= T_"+i+" 0.0) )\r\n" );
			}
			
			for( int i=0;i<pea.getClocks().size();i++ )
			{
				sb.append( "(assert (= "+pea.getClocks().get(i)+"_0 0.0) )\r\n" );
			}
			
			smtFile.write( sb.toString() );
		}catch( Exception e)
		{
			e.printStackTrace();
		
		}
    }
    
    private int indexOf( List<Transition> t, Phase dest )
    {
    	for( int i=0;i<t.size();i++ )
    	{
    		if( t.get(i).getDest()==dest )
    		{
    			return i;
    		}
    	}
    	return -1;
    }
    
	private void printStack( PhaseEventAutomata pea )
	{
		try{
			StringBuffer sb=new StringBuffer();
			sb.append( "\r\n(assert " );
			for( int i=0;i<st.size()-1;i++ )
			{
				Phase p=st.get(i);
				int idx=indexOf( p.getTransitions(), st.get(i+1) );
				if( idx<0 )
					return;
				
				Transition t=p.getTransitions().get(idx);
				sb.append( "(and (and ("+subst(p.getClockInvariant(),i)+") (and ("+subst( getTimed(t.getGuard()),i)+") (and (< T_"+i+" T_"+(i+1)+") ("+reset(t.getResets(), i, pea)+") )))" );
			}
			
			Phase p=st.peek();
			sb.append( "(and (and ("+subst(p.getClockInvariant(),(st.size()-1))+"))" );
			
			for( int i=0;i<st.size();i++ )
			{
				sb.append( ")" );
			}
			smtFile.write( sb.toString()+")\r\n" );
			
			writeDLcond( st.size()-1 );
			
			
			sb=new StringBuffer();
			sb.append( ";" );
			for( int i=0;i<st.size()-1;i++ )
			{
				sb.append( " " + st.get(i) );
			}
			
			smtFile.write( sb.toString()+")\r\n" );
			
		}
		catch(Exception e)
		{ 
			e.printStackTrace();
		}
	}
	
	private void writeDLcond( int k)
	{
		try{
			StringBuffer sb=new StringBuffer();
			
			sb.append( "(assert ("+subst( st.peek().dlCheck, k)+"))" );
			
			smtFile.write( sb.toString() );
		}
		catch(Exception e)
		{ 
			e.printStackTrace();
		}
	}
	
	
	private String subst(CDD cdd, int k)
	{
		String res= cdd.toSmtString(true,k);
		//for( int i=0;i<pea.getClocks().size();i++ )
		{
			//String pat=pea.getClocks().get(i);
			//res=res.replaceAll( "XXX", ((Integer)k).toString() );
		}
		return res;
	}
	
	private CDD getTimed(CDD cdd)
	{
		CDD[] res=getDisjuncts( cdd );
		CDD r=res[0];
		for( int i=1;i<res.length;i++ )
			r=r.or( res[i] );
		return r;
	}
	
	private Vector<CDD> disjuncts = new Vector<CDD>();
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
    
    private String reset( String[] reset, int start_k, PhaseEventAutomata pea )
	{
		StringBuffer sb=new StringBuffer();
		Vector<String> cl=new Vector<String>( pea.getClocks() );
		cl.removeAll( Arrays.asList(reset) );
		String[] terms=new String[ pea.getClocks().size() ];
		for( int i=0;i<reset.length;i++ )
		{
			terms[i]="(= "+reset[i]+"_"+(start_k+1)+" T_"+(start_k)+" )";
		}
		
		for( int i=0;i<cl.size();i++ )
		{
			terms[i+reset.length]="(= "+cl.get(i)+"_"+(start_k)+" "+cl.get(i)+"_"+(start_k+1)+" ) ";
		}
		
		for( int i=0;i<terms.length-1;i++)
		{
			sb.append( "(and " +terms[i] );
		}
		sb.append( " "+terms[terms.length-1] );
		
		for( int i=0;i<pea.getClocks().size()-1;i++)
		{
			sb.append( " ) " );
		}
		return sb.toString();
	}
}
