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
 * verwendet z3Interface um direkte ausgabe in z3 zu machen, 
 * setzt Pfade solange fort, bis grenze erreicht oder ziel gefunden 
 * 
 * Wie RTcheck12, daten werden aber direkt an z3 übergeben, statt in datei
 * 
 */
public class RTcheck14 {
	Stack<Phase> st;
	int maxlength=100;
	z3Interface z3;
	
	
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
	
	public RTcheck14()
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


	public boolean check( PhaseEventAutomata pea )
	{
		boolean res=false;
		try{
			z3=new z3Interface();
			st.clear();
			res= docheck( pea );
		}catch(Exception e)
		{
			e.printStackTrace();
		}
		z3.close();
		return res;
	}
	
	/*
	 * returns true if deadlock found
	 */
	private boolean docheck(PhaseEventAutomata pea )
	{
		try{
			z3.write( "(push)\r\n" );
			printHeader( pea );
			
			int n=Math.abs( rand.nextInt() ) % pea.getInit().length;
			st.push( pea.getInit()[n] );
			int minlen=1;//Math.abs( rand.nextInt() );
			int maxlen=2000;//Math.abs( rand.nextInt() );
			for( int i=1;i<maxlen;i++ )
			{
				Phase p=st.peek();
				
				printStepVars( pea, i );
				if( p.dlCheck!=CDD.FALSE  ) 
				{
					
					writeDLcond( i-1 ); // dl im vorigen schritt
				//	printStack( pea );
					if( z3.isSat() )
					{
						z3.getModel();
						z3.printModel();
						return true;
					}
					
				}
				
				// nächsten knoten suchen
				
				n=Math.abs( rand.nextInt() ) % ( p.getTransitions().size() );
				int k=n;
				Phase dest=p.getTransitions().get(n).getDest();
				while( dest==p )
				{
					n=(n+1)%( p.getTransitions().size() );
					if( n==k )
					{
						return false;
					}
					dest=p.getTransitions().get(n).getDest();
				}
				
				
				printStep( pea, i, p, n);
				
				// nächster knoten wurde gefunden
				st.push( dest );
			}
			
			
		}
		catch( Exception e )
		{
			e.printStackTrace();
		}
		
		return false;
	}
	
    
    private void printHeader( PhaseEventAutomata pea)
    {
    	try{
			z3.write( "(set-logic QF_RDL)\r\n\r\n" );

			printStepVars( pea, 0 );
			
			for( int i=0;i<pea.getClocks().size();i++ )
			{
				z3.write( "(assert (= "+pea.getClocks().get(i)+"_0 0.0) )\r\n" );
			}
			
		}catch( Exception e)
		{
			e.printStackTrace();
		
		}
    }
    
    private void printStepVars( PhaseEventAutomata pea, int step )
    {
    	StringBuffer sb=new StringBuffer();
    	sb.append( "(declare-funs (" );
		for( int i=0;i<pea.getClocks().size();i++ )
		{
			sb.append( "("+pea.getClocks().get(i)+"_"+step +" Real)" );
		}
		sb.append( "(T_"+step+" Real) ))\r\n" );
		
		
		sb.append( "(assert (> T_"+step+" 0.0) )\r\n" );
		z3.write( sb.toString() );
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
    
    private void printClockInv( Phase p, int step)
    {
    	z3.write( "(assert (and ("+subst(p.getClockInvariant(),(step))+"))\r\n" );
    }
    
	private void printStep( PhaseEventAutomata pea, int stepnum, Phase last, int idxnext )
	{
		try{
			StringBuffer sb=new StringBuffer();
			sb.append( "\r\n(assert " );
		//	for( int i=0;i<st.size()-1;i++ )
			{
				if( idxnext<0 )
					return;
				
				Transition t=last.getTransitions().get(idxnext);
				sb.append( "(and (and ("+subst(last.getClockInvariant(),stepnum-1)+") (and ("+subst( getTimed(t.getGuard()),stepnum-1)+") (and (< T_"+(stepnum-1)+" T_"+(stepnum)+") ("+reset(t.getResets(), stepnum-1, pea)+") ))))" );
			}
			
		//	Phase p=st.peek();
		//	sb.append( "(and (and ("+subst(p.getClockInvariant(),(st.size()-1))+"))" );
			

			z3.write( sb.toString()+")\r\n" );
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
			
			z3.write( sb.toString() );
		}
		catch(Exception e)
		{ 
			e.printStackTrace();
		}
	}
	
	
	private String subst(CDD cdd, int k)
	{
		String res= cdd.toSmtString(true, k);
		{
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
