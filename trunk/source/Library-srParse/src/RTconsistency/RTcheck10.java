package RTconsistency;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import pea.*;
import AdvancedPea.AdvPea;
import RTconsistency.RTcheck6.GI;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.Math;

/*
 * BMC mit Z3, für expliziten Parallelautmat
 * Quantorenfrei
 * 
 */
public class RTcheck10 {
	int bound;
	PhaseEventAutomata pea;
	
	BufferedWriter smtFile=null;
    
    private void setSmtFile(String filename)
    {
    	try {
			//messageFile=new BufferedWriter(new FileWriter(filename,"UTF8"));
    		smtFile = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename), "UTF8")); 
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	
    }

	public int getBound() {
		return bound;
	}

	public void setBound(int bound) {
		this.bound = bound;
	}
	
	public RTcheck10( int bound )
	{
		this.bound=bound;
	}
	
	public void check( PhaseEventAutomata pea, String filename )
	{
		try{
			this.pea=pea;
			setSmtFile( filename );
			generate_header();
			for( int i=0;i<bound;i++ )
				generate_timeprog(i);
			
			dl_cond();
			
			smtFile.write( "(check-sat)" );
			smtFile.write( "(model)" );
			
			smtFile.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void psi_q( int location, int curr_k )
	{
		
	}
	
	private void generate_header()
	{
		try{
			smtFile.write( "(set-logic QF_RDL)\r\n\r\n" );
			//(declare-funs ((c1_0 Real) (c2_0 Real) (c3_0 Real) (c4_0 Real) (T_0 Real)))
			StringBuffer sb=new StringBuffer();
			for( int k=0;k<=bound;k++)
			{
				
				sb.append( "(declare-funs (" );
				for( int i=0;i<pea.getClocks().size();i++ )
				{
					sb.append( "("+pea.getClocks().get(i)+"_"+k +" Real) ("+pea.getClocks().get(i)+"_"+k +"_ Real)" );
				}
				sb.append( "(T_"+k+" Real) (L_"+k+" Int) ))\r\n" );
				smtFile.write( sb.toString() );
				sb=new StringBuffer();
			}
			//StringBuffer sb=new StringBuffer();
			sb.append( "(assert (= T_0 0.0) )" );
			for( int i=1;i<=bound;i++ )
			{
				sb.append( "(assert (>= T_"+i+" 0.0) )" );
			}
			
			for( int i=0;i<pea.getClocks().size();i++ )
			{
				sb.append( "(assert (= "+pea.getClocks().get(i)+"_0 0.0) )" );
			}
			
			//for( int i=0;i<bound;i++ )
			{
				int i=0;
				//sb.append( "(assert (not (= L_"+i+" L_"+(i+1)+") ) )\r\n" );
				//sb.append(  );
			}
			
			
			smtFile.write( sb.toString() );
		}catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	private void generate_timeprog( int start_k )
	{
		try{
			StringBuffer sb=new StringBuffer();
			
			if( start_k==0 )
			{
				sb.append( "(assert " );
				for( int i=0;i<pea.getInit().length;i++ )
				{
					sb.append( "(or (=L_0 "+indexof(pea.getInit()[i])+")" );
				}
				for( int i=0;i<pea.getInit().length;i++ )
				{
					sb.append( ")" );
				}
				sb.append( ")\r\n" );
			}
			
			
			
		//	sb.append( "(assert " );
			sb.append( "(assert (and ("+getTimeProgDef( start_k )+") " );
			for( int i=0;i<pea.getPhases().length;i++ )
			{
				String buf=null;
				for( int j=0;j<pea.getPhases()[i].getTransitions().size();j++ )
				{
				//	buf=( "(and ("+getTimeProgDef( start_k )+") (and ("+subst(pea.getPhases()[i].getClockInvariant(), start_k)+") (and ("+subst(getTimed(pea.getPhases()[i].getTransitions().get(j).getGuard()), start_k)+") (and (= L_"+start_k+" "+i+") (and ("+reset( pea.getPhases()[i].getTransitions().get(j).getResets(), start_k )+") (= L_"+(start_k+1)+" "+indexof(pea.getPhases()[i].getTransitions().get(j).getDest())+"))))))" );
					buf=( "(and ("+subst(pea.getPhases()[i].getClockInvariant(), start_k)+") (and ("+subst(getTimed(pea.getPhases()[i].getTransitions().get(j).getGuard()), start_k)+") (and (= L_"+start_k+" "+i+") (and ("+reset( pea.getPhases()[i].getTransitions().get(j).getResets(), start_k )+") (= L_"+(start_k+1)+" "+indexof(pea.getPhases()[i].getTransitions().get(j).getDest())+")))))" );
					
					sb.append( "(or " ).append( buf.replaceAll( "T_XXX", "T_"+start_k) );
				}
				
				smtFile.write( sb.toString() );
				sb=new StringBuffer();
					
			}
			
			for( int i=0;i<pea.getPhases().length;i++ )
				for( int j=0;j<pea.getPhases()[i].getTransitions().size();j++ )
					sb.append( ")" );
			
		//	sb.append( ")\r\n" );
			sb.append( "))\r\n" );
			smtFile.write( sb.toString() );
			
		}
		catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	private int indexof( Phase p)
	{
		for( int i=0;i<pea.getPhases().length;i++ )
		{
			if( p==pea.getPhases()[i] )
				return i;
		}
		
		return -1;
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
	
	private String reset( String[] reset, int start_k )
	{
		StringBuffer sb=new StringBuffer();
		Vector<String> cl=new Vector<String>( pea.getClocks() );
		cl.removeAll( Arrays.asList(reset) );
		String[] terms=new String[ pea.getClocks().size() ];
		for( int i=0;i<reset.length;i++ )
		{
			terms[i]="(= "+reset[i]+"_"+(start_k+1)+" T_"+(start_k+1)+" )";
		}
		
		for( int i=0;i<cl.size();i++ )
		{
			terms[i+reset.length]="(= "+pea.getClocks().get(i)+"_"+start_k+"_ "+pea.getClocks().get(i)+"_"+(start_k+1)+" ) ";
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
	 
	
	private String getTimeProgDef( int start_k )
	{
		StringBuffer sb=new StringBuffer();
		
		for( int i=0;i<pea.getClocks().size()-1;i++)
		{
			sb.append( "(and (= "+pea.getClocks().get(i)+"_"+start_k+" "+pea.getClocks().get(i)+"_"+(start_k)+"_ ) " );
		}
		sb.append( "(and (= "+pea.getClocks().get( pea.getClocks().size()-1)+"_"+start_k+" "+pea.getClocks().get( pea.getClocks().size()-1 )+"_"+(start_k)+"_ ) (< T_"+start_k+" T_"+(start_k+1)+") )" );
		
		for( int i=0;i<pea.getClocks().size()-1;i++)
		{
			sb.append( ")" );
		}
		
		return sb.toString();
	}
	
	
	private void dl_cond( )
	{
		
		try{
			int cnt=0;
			StringBuffer sb=new StringBuffer();
			sb.append( "\r\n\r\n(assert " );
			for( int i=0;i<pea.getPhases().length;i++ )
			{
				if( pea.getPhases()[i].dlCheck!=CDD.FALSE )
				{
					cnt++;
					sb.append( "(or " );
					sb.append( dl_inner_cond( i, pea.getPhases()[i].dlCheck ) );
				}
				smtFile.write( sb.toString() );
				sb=new StringBuffer();
			}
			
			for( int i=0;i<cnt;i++ )
			{
				sb.append( ")" );
			}
			
			smtFile.write( sb.toString()+")\r\n" );
		}
		catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	private String dl_inner_cond( int L, CDD cond)
	{
		
		if( cond==CDD.FALSE )
			return "";
		
		StringBuffer sb=new StringBuffer();
		
		for( int i=1;i<=bound;i++ )
		{
			sb.append( "(or (and (= L_"+i+" "+L+") "+cond.toSmtString(true, i)+" )" );
		}
		for( int i=1;i<=bound;i++ )
			sb.append( ")" );
		//sb.append( ")\r\n" );
		
		return sb.toString();
		
	}
}

