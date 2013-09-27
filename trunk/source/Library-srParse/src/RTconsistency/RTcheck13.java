package RTconsistency;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.RangeDecision;
import pea.Transition;


/*
 * BMC mit Z3 für impliziten Parallelautomat
 * Parallelautomat wird von Z3 bestimmt
 * 
 * 
 * 
 */
public class RTcheck13 {
	int bound;
	PhaseEventAutomata[] pea;
	
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
    
    
    private Set<int[]> mindeadlocks=null;

	public void setMindeadlocks(Set<int[]> mindeadlocks) {
		this.mindeadlocks = mindeadlocks;
	}

	public int getBound() {
		return bound;
	}

	public void setBound(int bound) {
		this.bound = bound;
	}
	
	public RTcheck13( int bound )
	{
		this.bound=bound;
	}
	
	Vector<CDD> variables;
	
	public void check( PhaseEventAutomata[] pea, String filename, Vector<CDD> variables )
	{
		try{
			this.variables=variables;
			this.pea=pea;
			setSmtFile( filename );
			generate_header();
			for( int i=0;i<bound;i++ )
				generate_timeprog(i);
			
			dl_cond();
			
			smtFile.write( "(check-sat)\r\n" );
			smtFile.write( "(model)\r\n" );
			
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
			
			for( int j=0;j<pea.length;j++ )
			{
				for( int k=0;k<=bound;k++)
				{
					
					sb.append( "(declare-funs (" );
					for( int i=0;i<pea[j].getClocks().size();i++ )
					{
						sb.append( "("+pea[j].getClocks().get(i)+"_"+k +" Real) ("+pea[j].getClocks().get(i)+"_"+k +"_ Real)" );
					}
					sb.append( " (L_"+j+"_"+k+" Int) ))\r\n" );
					smtFile.write( sb.toString() );
					sb=new StringBuffer();
				}
				
				for( int i=0;i<pea[j].getClocks().size();i++ )
				{
					sb.append( "(assert (= "+pea[j].getClocks().get(i)+"_0 0.0) )" );
				}
			}
			
			sb.append( "(declare-funs (" );
			for( int i=0;i<=bound;i++ )
			{
				sb.append( "(T_"+i+" Real)" );
			}
			sb.append( "))\r\n" );
			
			//StringBuffer sb=new StringBuffer();
		//	sb.append( "(assert (= T_0 0.0) )" );
			for( int i=0;i<=bound;i++ )
			{
				sb.append( "(assert (> T_"+i+" 0.0) )" );
			}
			smtFile.write( sb.toString() );
			
			sb = new StringBuffer();
			sb.append( "(declare-funs (" );
			for( int i=0;i<variables.size();i++ )
			{
				for( int j=0;j<bound;j++ )
				{
					sb.append( "(" );
					sb.append( variables.get(i).getDecision().getSafeVar() );
					sb.append( "_"+j+" Bool)" );
				}
			}
			
			sb.append( "))" );
			smtFile.write( sb.toString() );
		}catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	
	int[] lastInit=null;
	private int[] getNextInit()
	{
		boolean inc=false;
		CDD inv=CDD.FALSE;
		if( lastInit==null )
		{
			lastInit=new int[pea.length];
			for( int i=0;i<lastInit.length;i++ )
			{
				lastInit[i]=0;
				inv=inv.and( pea[i].getInit()[0].getStateInvariant() );
			}
		}
		
		while(inv==CDD.FALSE && !inc)
		{
			inv=CDD.TRUE;
			inc=true;
			for( int i=0;i<pea.length;i++ )
			{
				if( inc )
				{
					lastInit[i]=lastInit[i]+1;
					if( lastInit[i]>=pea[i].getInit().length )
					{
						lastInit[i]=0;
					}
					else
						inc=false;
				}
				inv=inv.and( pea[i].getInit()[ lastInit[i] ].getStateInvariant() );
			}
		}
		
		if( inc || inv==CDD.FALSE )
		{
			return null;
		}
		
		return lastInit;
	}
	
	private void generate_timeprog( int start_k )
	{
		try{
			StringBuffer sb=new StringBuffer();
			int initcnt=0;

			if( start_k==0 )
			{
				int[] init;

				sb.append( "(assert " );
				init=getNextInit();
				while( init!=null )
				{
					initcnt++;
					sb.append( "(or " );
					for( int j=0;j<pea.length;j++ )
					{
						sb.append( "(and (=L_"+j+"_0 "+indexof(pea[j].getInit()[init[j]],j)+")" );
					}
					
					for( int i=0;i<pea.length;i++ )
					{
						sb.append( ")" );
					}
					
					init=getNextInit();
				}
				
				for( int i=0;i<initcnt;i++ )
				{
					sb.append( ")" );
				}
				
				
				if( initcnt==0 )
				{
					sb.append( " false)\r\n" );
				}
				else
					sb.append( ")\r\n" );
			}
			
			for( int ii=0;ii<pea.length;ii++ )
			{
				sb.append( "(assert (and ("+getTimeProgDef( start_k, ii )+") " );
				for( int i=0;i<pea[ii].getPhases().length;i++ )
				{
					String buf=null;
					for( int j=0;j<pea[ii].getPhases()[i].getTransitions().size();j++ )
					{
						String inv=pea[ii].getPhases()[i].getStateInvariant().toSmtString(true,start_k);
						buf=( "(and ("+subst(pea[ii].getPhases()[i].getClockInvariant(), start_k)+") (and ("+subst(getTimed(pea[ii].getPhases()[i].getTransitions().get(j).getGuard()), start_k)+") (and (= L_"+ii+"_"+start_k+" "+i+") (and ("+reset( pea[ii].getPhases()[i].getTransitions().get(j).getResets(), start_k, ii )+") (and (= L_"+ii+"_"+(start_k+1)+" "+indexof(pea[ii].getPhases()[i].getTransitions().get(j).getDest(),ii)+") ("+inv+") )))))" );
						//buf=" true ";
						
						sb.append( "(or " ).append( buf );
					}
					
					smtFile.write( sb.toString() );
					sb=new StringBuffer();
						
				}
				for( int i=0;i<pea[ii].getPhases().length;i++ )
					for( int j=0;j<pea[ii].getPhases()[i].getTransitions().size();j++ )
						sb.append( ")" );
				
				sb.append( ")\r\n" );
			}
			
			sb.append( "(assert (< T_"+start_k+" T_"+(start_k+1)+"))\r\n" );
			
			smtFile.write( sb.toString() );
			
		}
		catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	private int indexof( Phase p, int peaidx)
	{
		for( int i=0;i<pea[peaidx].getPhases().length;i++ )
		{
			if( p==pea[peaidx].getPhases()[i] )
				return i;
		}
		
		return -1;
	}
	
	private String subst(CDD cdd, int k)
	{
		String res= cdd.toSmtString(true, k);
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
	
	private String reset( String[] reset, int start_k, int peaidx )
	{
		StringBuffer sb=new StringBuffer();
		Vector<String> cl=new Vector<String>( pea[peaidx].getClocks() );
		cl.removeAll( Arrays.asList(reset) );
		String[] terms=new String[ pea[peaidx].getClocks().size() ];
		for( int i=0;i<reset.length;i++ )
		{
			terms[i]="(= "+reset[i]+"_"+(start_k+1)+" T_"+(start_k+1)+" )";
		}
		
		for( int i=0;i<cl.size();i++ )
		{
			terms[i+reset.length]="(= "+pea[peaidx].getClocks().get(i)+"_"+start_k+"_ "+pea[peaidx].getClocks().get(i)+"_"+(start_k+1)+" ) ";
		}
		
		for( int i=0;i<terms.length;i++)
		{
			sb.append( "(and " +terms[i] );
		}
		
		for( int i=0;i<terms.length;i++)
		{
			sb.append( " ) " );
		}
		return sb.toString();
	}
	 
	
	private String getTimeProgDef( int start_k, int peaidx )
	{
		StringBuffer sb=new StringBuffer();

		sb.append( "(and " );
		for( int i=0;i<pea[peaidx].getClocks().size();i++)
		{
			sb.append( "(and (= "+pea[peaidx].getClocks().get(i)+"_"+start_k+" "+pea[peaidx].getClocks().get(i)+"_"+(start_k)+"_ ) " );
		}
		
		
		for( int i=0;i<pea[peaidx].getClocks().size();i++)
		{
			sb.append( ")" );
		}
		
		
		for( int i=0;i<pea.length;i++)
		{
			sb.append( ")" );
		}
		
		return sb.toString();
	}
	
	
	private void dl_cond( )
	{
		
		try{
			
			for( int K=0;K<bound;K++)
			{
				StringBuffer sb=new StringBuffer();
				sb.append( "(assert " );
				
				for( Iterator<int[]> it=mindeadlocks.iterator();it.hasNext();)
				{
					int[] mdl=it.next();
					int len=0;
					
					for( int i=0;i<mdl.length;i++ )
					{
						if( mdl[i]>=0 )
						{
							sb.append( "(and (= L_"+i+"_"+K+" "+mdl[i]+") " );
						}
					}
					
					CDD cond=getMdlCond( mdl );
					sb.append( "("+cond.toSmtString(true,K)+")" );
					
					for( int i=0;i<mdl.length;i++ )
					{
						if( mdl[i]>=0 )
						{
							sb.append( ")" );
						}
					}
				}
				
				smtFile.write( sb.toString()+")\r\n" );
			}
			
			
		}
		catch( Exception e)
		{
			e.printStackTrace();
		
		}
	}
	
	private CDD getMdlCond( int[] mdl )
	{
		CDD res=CDD.TRUE;
		
		for( int i=0;i<mdl.length;i++ )
		{
			if( mdl[i]>=0 )
			{
				Phase p=pea[i].getPhases()[mdl[i]];
				res=res.and( p.getClockInvariant() );
				for( int j=0;j<p.getTransitions().size();j++ )
				{
					Transition t=p.getTransitions().get(j);
					res=res.and( getTimed( t.getGuard() ) );
				}
			}
		}
		
		return res;
	}
}
