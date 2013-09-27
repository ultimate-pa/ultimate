package srParse;

	import java.io.BufferedWriter;
import java.io.FileOutputStream;
	import java.io.FileWriter;
	import java.io.IOException;
import java.io.OutputStreamWriter;
	import java.util.List;
	import java.util.Vector;

import pea.*;

	public class RTcheck1 {
	/**

	 */

		
		 private Vector<CDD> disjuncts = new Vector<CDD>();
		 private String initialState = "initialState";
		 protected int transCount = 0;
		
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
	    	   
	    	Vector<Transition> transitions = new Vector<Transition>();   
	   	 
	    	for(int i=0; i<phases.length; i++) {
	    		Phase phase = phases[i];
	    		transitions.addAll(phase.getTransitions());
	       }    
	   	 
	    	this.transCount = transitions.size();
	    	for (int j=0; j<transCount; j++){
	    		Transition trans = transitions.elementAt(j);
	    		
	    		if( trans.getSrc()==trans.getDest() )
	    			continue;
	    		
	    		if( trans.getSrc().getClockInvariant()==CDD.TRUE )
	    			trans.getSrc().dlCheck=CDD.FALSE;
	    		
	    		if( trans.getSrc().dlCheck==CDD.FALSE )
	    			continue;
	    		
	    		
	    		
	    		this.createPEATransitionString(trans);
	    	}       
	    	
	       }
	    
	    
	    /* todo: sonderfall: in der location ist nur eine clock vorhanden und
	     * Bsp: CI(State)= c<=5 und die Ausgehenden guards haben die guards
	     * c>=5 die dests sind nicht von c abhÃ¤ngig, dann bleibt c<5, obwohl kein DL existiert
	     */
	    protected void createPEATransitionString(Transition transition){
	        CDD[] disjuncts = this.getDisjuncts(transition.getGuard());        
	        String[] resets = transition.getResets();
	        
	        for(int i=0;i<disjuncts.length;i++)
	        {
	        	if( disjuncts[i]==CDD.FALSE  )
	        		continue;
	        	
	        	if( disjuncts[i]==CDD.TRUE  )
	        	{
	        		transition.getSrc().dlCheck=CDD.FALSE;
	        		break;
	        	}
	        	
	        	CDD t;
	        	
	        	if( transition.getDest().getClockInvariant()==CDD.TRUE )
	        		t=transition.getSrc().dlCheck.and( disjuncts[i].negate() );
	        	else
	        		t=transition.getSrc().dlCheck.and( disjuncts[i].and( transition.getDest().getClockInvariant() ).negate() );
	        	
	        	for( int j=0;j<resets.length;j++ )
	        	{
	        		CDD res=RangeDecision.create( resets[j], RangeDecision.OP_EQ, 0 );
	        		t=t.assume( res );
	        	}
	        	
	        	
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
	    
	    public void checkPea(PhaseEventAutomata pea) {    	
	    	
	        //First we need to simplify some guards
	        pea.simplifyGuards();
	        createPEAString(pea);
	        
	        try
	        {
		        for( int i=0;i<pea.getPhases().length;i++ )
		        {
		        	CDD cdd=pea.getPhases()[i].dlCheck;
		        	if( cdd!=CDD.FALSE )
		        	{
		        		String line="DL2: Detected Deadlock in location: " + pea.getPhases()[i].getName() + "  (" + cdd + ")\r\n";
		        		if( messageFile!=null )
		        		{
							messageFile.write(line);
							System.out.println(line);
		        		}
		        		System.err.print( line );
		        	}
		        	
		        	
		        }
		        
		        if( messageFile!=null )
		        	messageFile.flush();
		    } catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		    
		    
	    }
	    
	    
	    

	}

	
	
	
	
	
	
	
	