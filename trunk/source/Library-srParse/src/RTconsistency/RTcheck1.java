package RTconsistency;

	import java.io.BufferedWriter;
import java.io.FileOutputStream;
	import java.io.FileWriter;
	import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.reflect.Array;
import java.util.Arrays;
	import java.util.List;
	import java.util.Vector;


import pea.*;



/*
 * Momentan wird nur Innerclass GI verwendet (durch andere Klassen)
 * 
 */

	public class RTcheck1 {
	/**

	 */

		
		 private Vector<CDD> disjuncts = new Vector<CDD>();
		 private String initialState = "initialState";
		 protected int transCount = 0;
		 
		 
		 private boolean isClockDependend( CDD cdd )
		 {
			 boolean res=false;
			 
			 if( cdd.getDecision() instanceof RangeDecision )
				 return true;
			 
			 if( cdd.getChilds()!=null )
			 {
				for(int i=0;i<cdd.getChilds().length;i++)
				{
					res|= isClockDependend( cdd.getChilds()[i] );
				}
			 }
			 return res; 
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
	    
	    //add the transitions of the pea
	    protected void addPEATransitions(Phase[] phases) {
	    	   
	    	List<Transition> transitions;   
	   	 
	    	for(int i=0; i<phases.length; i++) {
	    		Phase phase = phases[i];
	    		transitions=(phase.getTransitions());
	       
		    	for (int j=0; j<transitions.size(); j++){
		    		Transition trans = transitions.get(j);
		    		
		    		//if( trans.getSrc()==trans.getDest() )
		    			//continue;
		    		
		    		if( trans.getSrc().getClockInvariant()==CDD.TRUE )
		    		{
		    			trans.getSrc().haslDl=false;
		    			trans.getSrc().dlCheck=CDD.FALSE;
		    		}
		    		
		    		if( trans.getSrc().dlCheck==CDD.FALSE && !trans.getSrc().haslDl ) 
		    			continue;
		    		
		    		this.createPEATransitionString(trans);
		    	}    
	    	}
	    	
	       }
	    
	    

	    protected void createPEATransitionString(Transition transition){
	        CDD[] disjuncts = this.getDisjuncts(transition.getGuard());        
	        String[] resets = transition.getResets();
	        
	        for(int i=0;i<disjuncts.length;i++)
	        {
	        	if( disjuncts[i]==CDD.FALSE  )
	        		continue;
	        	
	        	if( disjuncts[i]==CDD.TRUE  )
	        	{
	        		if( transition.getSrc()!=transition.getDest() )
	        		{
	        			transition.getSrc().haslDl=false;
	        			transition.getSrc().dlCheck=CDD.FALSE;
	        		}
	        		break; 
	        	}
	        	
	        	if( ( transition.getSrc()!=transition.getDest() ) && !isClockDependend( disjuncts[i] ) )
	        	{
	        		transition.getSrc().haslDl=false;
	        	}
	        	
	        	CDD t;
	        	
	        	if( transition.getDest().getClockInvariant()==CDD.TRUE )
	        	{
	        		t=transition.getSrc().dlCheck.and( disjuncts[i].negate() );
	        	}
	        	else
	        	{
	        		CDD ttt=transition.getDest().getClockInvariant();//  für  allegemeine PEA muss transition.getDest().getClockInvariant() strict gemacht werden, 
	        							// für die aus Anf generierten gehts auch so
	        		for( int j=0;j<resets.length;j++ )
	        		{
	        			CDD as=RangeDecision.create(resets[j], RangeDecision.OP_EQ, 0);
	        			ttt.assume( as );
	        		}
	        		CDD tt=disjuncts[i].and( ttt );   
	        		//CDD tt=disjuncts[i];
	        		t=transition.getSrc().dlCheck.and( tt.negate() );
	        	}
	        	
	        	/*for( int j=0;j<resets.length;j++ )
	        	{
	        		CDD res=RangeDecision.create( resets[j], RangeDecision.OP_EQ, 0 );
	        		t=t.assume( res );
	        	}*/
	        	
	        	transition.getSrc().dlCheck=t;
	        }
	    }
	    
	    
	    
	    protected void createPEAString(PhaseEventAutomata pea){
	        Phase[] phases = pea.getPhases();
	        addPEATransitions(phases);
	    }
	    
	    BufferedWriter messageFile=null;
	    
	    public void setMessageFile(String filename)
	    {
	    	try {
				//messageFile=new BufferedWriter(new FileWriter(filename,"UTF8"));
				messageFile = new BufferedWriter(new OutputStreamWriter( new FileOutputStream(filename), "UTF8")); 
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	    	
	    }
	    
	    
		private int indexOf( Phase[] phases, Phase p )
		{
			for( int i=0;i<phases.length;i++ )
			{
				if( p== phases[i] )
					return i;
			}
			return -1;
		}
	    
	    public void checkPea(PhaseEventAutomata pea) {    	
	    	
	        //First we need to simplify some guards
	        pea.simplifyGuards();
	        createPEAString(pea);
	        
	        try
	        {
	        	for( int i=0;i<pea.getInit().length;i++ )
	        	{
	        		pea.getInit()[i].setInit( true );
	        	}
	        		
	        		
		        for( int i=0;i<pea.getPhases().length;i++ )
		        {
		        	CDD cdd=pea.getPhases()[i].dlCheck;
		        	if( cdd!=CDD.FALSE ) //isLocalDeadlock( cdd ) )
		        	{
		        		//boolean isInit=indexOf( pea.getInit(), pea.getPhases()[i] ) >=0;
		        		/*if( isGlobalDeadlock( cdd, pea.getPhases()[i].isInit() ) )
		        		{
		        			String line="DL2: Detected global Deadlock in location: " + pea.getPhases()[i].getName() + "  (" + cdd + ") ("+i+")\r\n";
			        		if( messageFile!=null )
			        		{
								messageFile.write(line);
			        		}
			        		System.err.print( line );
		        		}
		        		else
		        		{*/
			        		String line="Detected D0 Deadlock in location: " + pea.getPhases()[i].getName() + "  (" + cdd + ")("+i+")\r\n";
			        		if( messageFile!=null )
			        		{
								messageFile.write(line);
			        		}
			        		System.out.print( line );
			        		
			        		if( !pea.getPhases()[i].haslDl  )
				        	{
				        		System.out.println( "pea.getPhases()[i].haslDl != (cdd==CDD.FALSE) " + pea.getPhases()[i].getName() );
				        	}
		        		//}
		        	}
		        	else
		        	{
		        		if( pea.getPhases()[i].haslDl  )
			        	{
			        		System.out.println( "pea.getPhases()[i].haslDl != (cdd==CDD.FALSE) " + pea.getPhases()[i].getName() );
			        	}
		        	}
		        	
		        	
		        	
		        	
		        }
		        
		        if( messageFile!=null )
		        	messageFile.flush();
		    } catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		    
		    
	    }
	    
	    /*
	     * 	Erwartet cdd in dnf
	     * 
	     */
	    private boolean isLocalDeadlock( CDD cdd )
	    {
	    	if( cdd.getChilds()==null )
	    		return false;
	    	
	    	if( cdd.getOp()==RangeDecision.OP_EQ )
			{
				return true;
			}
	    	
	    	for( int i=0;i<cdd.getChilds().length;i++ )
	    	{	   
	    		CDD c=cdd.getChilds()[i];
	    		return isLocalDeadlock( c );
	    	}
	    	
	    	return false;
	    }
	    
	    
	    private int min( int a, int b )
	    {
	    	return a<b ? a : b;
	    }
	    
	    private int max( int a, int b )
	    {
	    	return a<b ? b : a;
	    }
	    
	    /*
	     * True - es liegt sicher ein globaler D vor
	     * False - keine Aussage
	     * 
	     */
	   /* private boolean isGlobalDeadlock( CDD cdd, boolean isInitial )
	    {
	    	if( cdd.getDepth()==1 )
	    	{
	    		return true;
	    	}
	    	
	    	
	    	// * Alle Entscheidungen mit == haben die gleiche Bound UND diese ist die kleinste aller vorhandenden clocks
	    	
	    	if( isInitial )
	    	{
	    		int maxeq=0;
	    		int minother=-1;
	    		CDD cd=cdd;
	    		while( cd.getChilds()!=null )
	    		{
		    		for( int i=0;i<cd.getChilds().length;i++ )
			    	{
			    		CDD c=cd.getChilds()[i];
			    		if( c!=CDD.FALSE )
			    		{
			    			if( cd.getDecision() instanceof RangeDecision )
			    			{
			    				if( ((RangeDecision)cd.getDecision()).getOp(i)==RangeDecision.OP_EQ )
			    				{
			    					maxeq=max( ((RangeDecision)cd.getDecision()).getVal(i), maxeq );
			    				}
			    				else
			    				{
			    					if( minother<0 )
			    						minother=((RangeDecision)cd.getDecision()).getVal(i);
			    					else
			    						minother=min( minother, ((RangeDecision)cd.getDecision()).getVal(i) );
			    				}
			    			}
			    			cd=c;
			    			break;
			    		}
			    	}
	    		}
	    		
	    		if( maxeq<minother )
	    			return true;
	    	}
	    	
	    	return false;
	    }*/

	}

	
	
	
	
	
	
	
	