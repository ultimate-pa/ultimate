package pea.test;

import pea.BooleanDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.EventDecision;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
import pea.modelchecking.DOTWriter;
import pea.modelchecking.J2UPPAALConverter;
import pea.modelchecking.MCTrace;

public class TestUppaalExport {
	
	Trace2PEACompiler compiler = new Trace2PEACompiler();
    CDD entry = EventDecision.create("S1");
    //CDD entry = CDD.FALSE;
    CDD exit = EventDecision.create("S2");
    //CDD exit = CDD.TRUE;
    CDD missing = CDD.TRUE;
    
	
	public PhaseEventAutomata bndInvariance(CDD P, CDD S, int bound) {
    	PhaseEventAutomata ctA, ctA2, mctA, mctA2;
    	CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    	    new CounterTrace.DCPhase(),
    	    new CounterTrace.DCPhase(P),
    	    new CounterTrace.DCPhase(S, CounterTrace.BOUND_LESS, bound),
    	    new CounterTrace.DCPhase(S.negate()),
    	    //new CounterTrace.DCPhase(R),
    	    new CounterTrace.DCPhase()
    	});
    	MCTrace mct = new MCTrace(ct, entry, exit, missing, true);
    	mctA = compiler.compile("TInvariance1", mct); //ctA.dump();
    	ctA = compiler.compile("TInvariance1", ct); //ctA.dump();
    	
    	CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    	    new CounterTrace.DCPhase(),
    	    new CounterTrace.DCPhase(P.and(S.negate())),
    	    new CounterTrace.DCPhase()
    	});
    	
    	ctA2 = compiler.compile("TInvariance2", ct2); 
    	//ctA2.dump();
    	ctA = ctA2.parallel(ctA); //ctA.dump();
    	return ctA;
    	//return mctA;
        }
	
	 public PhaseEventAutomata bndResp_Glob(CDD P, CDD S, int bound) {
	    	PhaseEventAutomata ctA;
	    	CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(P.and(S.negate())),
	    	    new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, bound),
	    	    new CounterTrace.DCPhase()
	    	});
	    	ctA = compiler.compile("TBndResp", ct); //ctA.dump();
	    	return ctA;

	        }
	
	public void testUppaal(){
    	PhaseEventAutomata ctParallel, ct1A, ct2A;
        CDD P = BooleanDecision.create("P");
    	CDD S = BooleanDecision.create("S");
    	
    	ct1A = bndInvariance(P, S.negate(),6);   
        ct2A = bndResp_Glob(P,S,10);
       
        ctParallel = ct1A.parallel(ct2A);
        ctParallel.dump();
        
        DOTWriter dotwriter = new DOTWriter("C:/Deadlock.dot", ctParallel);
        dotwriter.write();
        
        J2UPPAALConverter j2uppaalWriter = new J2UPPAALConverter();
        j2uppaalWriter.writePEA2UppaalFile("C:/AmiTestDeadlock.xml", ctParallel);        
        
    }
	
	public void run(){
		testUppaal();
	}
	
	public static void main(String[] param) {
		org.apache.log4j.PropertyConfigurator.configure
		    (ClassLoader.getSystemResource("pea/test/TestLog.config"));
		new TestUppaalExport().run();
		
	    }

}
