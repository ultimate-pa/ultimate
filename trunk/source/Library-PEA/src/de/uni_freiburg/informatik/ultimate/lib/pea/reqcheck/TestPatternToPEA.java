package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PEACompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DOTWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALWriter;

public class TestPatternToPEA {

	/**
	 * @param args
	 */
	PatternToPEA patternToPEA = new PatternToPEA(ILogger.getLogger(""));
	static final CDD P = BooleanDecision.create("P");
	static final CDD Q = BooleanDecision.create("Q");
	static final CDD R = BooleanDecision.create("R");
	static final CDD S = BooleanDecision.create("S");
	static final CDD T = BooleanDecision.create("T");
	
	DOTWriter dotwriter = new DOTWriter("C:/test/TestPatternToPEA.dot");
	J2UPPAALConverter j2uppaalWriter = new J2UPPAALConverter();
    

	
	
    

    
    
    
    
    
    public void consistencyTest(){
    	PhaseEventAutomata a1, a2, a3, aParallel;
    	a1 = patternToPEA.absencePattern(P, Q, R, "Globally");
    	a2 = patternToPEA.universalityPattern(P, Q, R, "Globally");
    	a3 = patternToPEA.bndInvariancePattern(T, Q, R, S, 10, "Globally");
    	aParallel = a1.parallel(a3).parallel(a2);
    	dotwriter.write("C:/vacuous/testConsistency.dot", aParallel);
    	
    }
    
    public void vacuousTest(){
    	PhaseEventAutomata ct1A, ct2A, ctParallel;
    	final CDD A = BooleanDecision.create("A");
    	final CDD B = BooleanDecision.create("B");
        
        ct1A = patternToPEA.invariantPattern(A,B,A,B,"Globally");
        ct2A = patternToPEA.invariantPattern(A,B,A,B.negate(),"Globally");
        ctParallel = ct1A.parallel(ct2A);
        dotwriter.write("C:/vacuous/vac1.dot", ct1A);
        dotwriter.write("C:/vacuous/vac2.dot", ct2A);
        ct2A.dump();
        dotwriter.write("C:/vacuous/vac12.dot", ctParallel);
    }
    
    public void vacuousTest3(){
    	PhaseEventAutomata ct1A;
		final PhaseEventAutomata ct2A, ctParallel;
        ct1A = patternToPEA.universalityPattern(P.and(Q), Q, R, "After");
        //ct2A = patternToPEA.universalityPattern(P, Q.negate(), R, "After");
        //ctParallel = ct1A.parallel(ct2A);
        dotwriter.write("C:/vacuous/vacTest3.dot", ct1A);
    }
    
	
	public PhaseEventAutomata vacuousTest2(){
    	PhaseEventAutomata ct1A, ct2A, ctParallel;
    	final CDD P = BooleanDecision.create("P");
    	final CDD S = BooleanDecision.create("S");
        
        ct1A = patternToPEA.bndInvariancePattern(P,P,P,S,10,"Globally");
        ct2A = patternToPEA.universalityPattern(P,S,S,"After");
        ctParallel = ct1A.parallel(ct2A);
        dotwriter.write("C:/vacuous/vac2_1.dot", ct1A);
        dotwriter.write("C:/vacuous/vac2_2.dot", ct2A);
        dotwriter.write("C:/vacuous/vac2_12.dot", ctParallel);
        j2uppaalWriter.writePEA2UppaalFile("C:/vacuous/vac2_12.xml", ctParallel);
        return ctParallel;
    }
	
	public PhaseEventAutomata vacuousTest22(){
    	PhaseEventAutomata ct1A, ct2A, ctParallel;
    	final CDD P = BooleanDecision.create("velocity<10");
    	final CDD S = BooleanDecision.create("standstill");
        
        ct1A = patternToPEA.bndInvariancePattern(P,P,P,S,10,"Globally");
        ct2A = patternToPEA.universalityPattern(P,S,S,"After");
        ctParallel = ct1A.parallel(ct2A);
        dotwriter.write("C:/vacuous/BspPaper_1.dot", ct1A);
        dotwriter.write("C:/vacuous/BspPaper_2.dot", ct2A);
        dotwriter.write("C:/vacuous/BspPaper_12.dot", ctParallel);
        j2uppaalWriter.writePEA2UppaalFile("C:/vacuous/BspPaper_12.xml", ctParallel);
        return ctParallel;
    }
	
	//Beispiel um Deadlock zu provozieren:
	//Beispiel mit infinite und finite runs
    public void testUppaal(){
    	PhaseEventAutomata ctParallel, ct1A, ct2A;
        final CDD P = BooleanDecision.create("IRTest");
    	final CDD S = BooleanDecision.create("IRLampsOn");
    	final CDD Q = BooleanDecision.create("Q");
    	final CDD R = BooleanDecision.create("R");
    	
    	ct1A = patternToPEA.bndInvariancePattern(P,Q,R,S.negate(),6, "Globally");
        ct2A = patternToPEA.bndResponsePattern(P,Q,R,S,10, "Globally");
        ctParallel = ct1A.parallel(ct2A);
        ctParallel.dump();
        
        final J2UPPAALConverter j2uppaalConverter = new J2UPPAALConverter();
        j2uppaalConverter.writePEA2UppaalFile("C:/vacuous/deadlock/AmiTestDeadlock.xml", ctParallel);
        
        dotwriter.write("C:/vacuous/deadlock/d1.dot", ct1A);
        dotwriter.write("C:/vacuous/deadlock/d2.dot", ct2A);
        dotwriter.write("C:/vacuous/deadlock/d12.dot", ctParallel);
        
    }
    
    //Beispiel von oben, + zus�tzliche Anforderungen, die den Deadlock ausschlie�en
    public void testUppaal2(){
    	PhaseEventAutomata ctParallel, ct1A, ct2A;
		final PhaseEventAutomata ct3A;
		PhaseEventAutomata ct4A, ct5A;
        final CDD P = BooleanDecision.create("IRTest");
    	final CDD S = BooleanDecision.create("IRLampsOn");
    	final CDD Q = BooleanDecision.create("Q");
    	final CDD R = BooleanDecision.create("R");
    	
    	ct1A = patternToPEA.bndInvariancePattern(P,Q,R,S.negate(),6, "Globally");
        ct2A = patternToPEA.bndResponsePattern(P,Q,R,S,10, "Globally");
       // ct3A = patternToPEA.invariantPattern(P, Q, R, S.negate(), "Globally");
        ct4A = patternToPEA.maxDurationPattern(P, Q, R, 3, "Globally");
        ct5A = patternToPEA.minDurationPattern(P.negate(), Q, R, 10, "Globally");
        //ctParallel = ct1A.parallel(ct2A).parallel(ct3A).parallel(ct4A);
        //ctParallel.dump();
        
 //       ctParallel = ct1A.parallel(ct2A).parallel(ct3A);
        
        final J2UPPAALConverter j2uppaalConverter = new J2UPPAALConverter();
        //J2UPPAALConverterDOM j2uppaalConverterDom = new J2UPPAALConverterDOM();
        //J2UPPAALWriterV4 j2uppaalWriter = new J2UPPAALWriterV4();
 //       j2uppaalConverter.writePEA2UppaalFile("C:/vacuous/deadlock/d123.xml", ctParallel);
 //       dotwriter.write("C:/vacuous/deadlock/d2_123.dot", ctParallel);
        
        ctParallel = ct1A.parallel(ct2A);
        j2uppaalConverter.writePEA2UppaalFile("C:/vacuous/deadlock/ex2/d12_n.xml", ctParallel);
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_12n.dot", ctParallel);
        //ctParallel=ctParallel.parallel(ct3A);
        //dotwriter.write("C:/vacuous/deadlock/ex2/d2_123n.dot", ctParallel);
        
        ctParallel = ctParallel.parallel(ct4A).parallel(ct5A);
        j2uppaalConverter.writePEA2UppaalFile("C:/vacuous/deadlock/ex2/d1234_n.xml", ctParallel);
        
        //j2uppaalConverter.writePEA2UppaalFile("C:/vacuous/deadlock/d2.xml", ct2A);
        
        //j2uppaalWriter.writePEA2UppaalFile("C:/vacuous/deadlock/d1234_V4.xml", ctParallel);
        //j2uppaalConverterDom.create("C:/vacuous/deadlock/d1234_DOM.xml", ctParallel);
        
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_1n.dot", ct1A);
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_2n.dot", ct2A);
        //dotwriter.write("C:/vacuous/deadlock/ex2/d2_3n.dot", ct3A);
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_4n.dot", ct4A);
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_5n.dot", ct5A);
        dotwriter.write("C:/vacuous/deadlock/ex2/d2_12345.dot", ctParallel);
        
        //ctParallel = ct1A.parallel(ct3A);
        //dotwriter.write("C:/vacuous/deadlock/ex2/d2_13n.dot", ctParallel);
        
    }
    
    public void testDeadlock(){
    	PhaseEventAutomata ctParallel, ct1A, ct2A, ct3A;
        final CDD P = BooleanDecision.create("P");
    	final CDD S = BooleanDecision.create("S");
    	final CDD Q = BooleanDecision.create("Q");
    	final CDD R = BooleanDecision.create("R");
    	
    	ct1A = patternToPEA.absencePattern(S, Q, R, "Globally");
        ct2A = patternToPEA.bndResponsePattern(P,Q,R,S,10, "Globally");
        ct3A = patternToPEA.universalityPattern(P, Q, R, "Globally");
        ctParallel = ct1A.parallel(ct2A).parallel(ct3A);
        ctParallel.dump();
        
        final J2UPPAALWriter j2uppaalWriter = new J2UPPAALWriter();
        j2uppaalWriter.writePEA2UppaalFile("C:/vacuous/deadlock/d34.xml", ct1A);
        
        dotwriter.write("C:/vacuous/deadlock/d3.dot", ct1A);
        dotwriter.write("C:/vacuous/deadlock/d4.dot", ct2A);
        dotwriter.write("C:/vacuous/deadlock/d34.dot", ctParallel);
        
    }
    
    
    
    
    public void testBeforeScope(){
    	final CDD P = BooleanDecision.create("P");
    	final CDD S = BooleanDecision.create("S");
    	final CDD T = BooleanDecision.create("T");
    	final CDD R = BooleanDecision.create("R");
    	final CDD Q = BooleanDecision.create("Q");
    	PhaseEventAutomata ct;
    	
    	final DOTWriter dotwriter = new DOTWriter("C:\test\before.dot");
    	
    	ct = patternToPEA.absencePattern(P, Q, R, "Before");
    	dotwriter.write("C:/test/absenceBefore.dot", ct);
    	ct = patternToPEA.universalityPattern(P, Q, R, "Before");
    	dotwriter.write("C:/test/universBefore.dot", ct);
    	ct = patternToPEA.bndExistencePattern(P, Q, R, "Before");
    	dotwriter.write("C:/test/bndExistenceBefore.dot", ct);
    	ct = patternToPEA.precedencePattern(P, Q, R, S, "Before");
    	dotwriter.write("C:/test/precedenceBefore.dot", ct);
    	ct = patternToPEA.precedenceChainPattern12(P, Q, R, S, T,"Before");
    	dotwriter.write("C:/test/precedenceChain12Before.dot", ct);
    	ct = patternToPEA.invariantPattern(P, Q, R, S,"Before");
    	dotwriter.write("C:/test/invariantBefore.dot", ct);
    	ct = patternToPEA.responseChainPattern21(P, Q, R, S,T,"Before");
    	dotwriter.write("C:/test/respChain21Before.dot", ct);
    	
    	ct = patternToPEA.minDurationPattern(P, Q, R, 10 ,"Before");
    	dotwriter.write("C:/test/minDurBefore.dot", ct);
    	ct = patternToPEA.maxDurationPattern(P, Q, R, 10,"Before");
    	dotwriter.write("C:/test/maxDurBefore.dot", ct);
    	ct = patternToPEA.bndResponsePattern(P, Q, R, S, 10,"Before");
    	dotwriter.write("C:/test/bndRespBefore.dot", ct);
    	ct = patternToPEA.bndInvariancePattern(P, Q, R, S, 10,"Before");
    	dotwriter.write("C:/test/bndInvBefore.dot", ct);
    	ct = patternToPEA.periodicPattern(P, Q, R, 10,"Before");
    	dotwriter.write("C:/test/periodicBefore.dot", ct);
    	
    	ct = patternToPEA.precedenceChainPattern21(P, Q, R, S,T,"Globally");
    	dotwriter.write("C:/test/precChain21Before.dot", ct);
    	
    }
    
    public void testSeeping(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata a1, a2, a3;
    	
    	a1 = patternToPEA.universalityPattern(P, Q, R, "Between");
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(Q.and(R.negate())),
	    	    new CounterTrace.DCPhase(R.negate()),
	    	    new CounterTrace.DCPhase(P.negate().and(R.negate())),
	    	    new CounterTrace.DCPhase(R.negate()),
	    	    //new CounterTrace.DCPhase(R),
	    	    new CounterTrace.DCPhase()
	    	});
	    a2 = compiler.compile("univBet2", ct); //ctA.dump();
	    
	    final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(Q.and(R.negate())),
	    	    new CounterTrace.DCPhase(R.negate()),
	    	    new CounterTrace.DCPhase(P.negate().and(R.negate())),
	    	    //new CounterTrace.DCPhase(R.negate()),
	    	    //new CounterTrace.DCPhase(R),
	    	    new CounterTrace.DCPhase()
	    	});
	    a3 = compiler.compile("univBet3", ct2); //ctA.dump();
	    dotwriter.write("C:/vacuous/univBet.dot", a1);
	    dotwriter.write("C:/vacuous/univBet2.dot", a2);
	    dotwriter.write("C:/vacuous/univBet3.dot", a3);
	    
	    //-->zeigt: geseepte Phasen am Ende fallen weg (ct2 und ct f�hren zum selben Automaten)
    }
    
    public void testSeeping2(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata a1, a2, a3;
    	
    	a1 = patternToPEA.bndExistencePattern(P, Q, R, "Before");
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(R.negate()),
     		    new CounterTrace.DCPhase(P.and(R.negate())),
     		    new CounterTrace.DCPhase(P.negate().and(R.negate())),
     		    new CounterTrace.DCPhase(P.and(R.negate())),
     		    new CounterTrace.DCPhase(P.negate().and(R.negate())),
     		    //new CounterTrace.DCPhase(P.and(R.negate())),
    		    new CounterTrace.DCPhase()
    		 });
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(R.negate()),
     		    new CounterTrace.DCPhase(P.and(R.negate())),
     		    new CounterTrace.DCPhase(P.negate().and(R.negate())),
     		    new CounterTrace.DCPhase(P.and(R.negate())),
     		    //new CounterTrace.DCPhase(P.negate().and(R.negate())),
     		    //new CounterTrace.DCPhase(P.and(R.negate())),
    		    new CounterTrace.DCPhase()
    		 });
    	a2 = compiler.compile("test", ct); //ctA.dump();
	    a3 = compiler.compile("test2", ct2); //ctA.dump();
	    dotwriter.write("C:/vacuous/bndExistBef.dot", a1);
	    dotwriter.write("C:/vacuous/bndExistBef2.dot", a2);
	    dotwriter.write("C:/vacuous/bndExistBef3.dot", a3);
	    
	    //-->zeigt: in diesem Fall f�llt jeweils der Zustand der letzten Phase weg
    }
    
    public PhaseEventAutomata testBndInvarianceVacuous(){
    	PhaseEventAutomata ct2A, ctA;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(P),
	    	    new CounterTrace.DCPhase(S),
	    	    new CounterTrace.DCPhase(S.negate()),
	    	    new CounterTrace.DCPhase()
	    	});
    		final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
	    	ctA = compiler.compile("inv1", ct); //ctA.dump();
	    	
	    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(P.and(S.negate())),
	    	    new CounterTrace.DCPhase()
	    	});
	    	ct2A = compiler.compile("inv2G", ct2);
	    	//ctA2.dump();
	    	ctA = ct2A.parallel(ctA); //ctA.dump();
	    	return ctA;
    }
    
    public void testSeeping3(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata a1, a2, a3;
    	
    	a1 = patternToPEA.bndExistencePattern(P, Q, R, "After");
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
     		    new CounterTrace.DCPhase(Q),
     		    new CounterTrace.DCPhase(),
     		    new CounterTrace.DCPhase(P),
     		    new CounterTrace.DCPhase(P.negate()),
     		    new CounterTrace.DCPhase(P),
     		    new CounterTrace.DCPhase(P.negate()),
    		    //new CounterTrace.DCPhase(P),
    		    new CounterTrace.DCPhase()
    		 });
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
     		    new CounterTrace.DCPhase(Q),
     		    new CounterTrace.DCPhase(),
     		    new CounterTrace.DCPhase(P),
     		    new CounterTrace.DCPhase(P.negate()),
     		    new CounterTrace.DCPhase(P),
    		    new CounterTrace.DCPhase()
    		 });
    	a2 = compiler.compile("test", ct); //ctA.dump();
	    a3 = compiler.compile("test2", ct2); //ctA.dump();
	    dotwriter.write("C:/vacuous/bndExistAf.dot", a1);
	    dotwriter.write("C:/vacuous/bndExistAf2.dot", a2);
	    dotwriter.write("C:/vacuous/bndExistAf3.dot", a3);
	    
	    //-->zeigt: in diesem Fall f�llt jeweils der Zustand der letzten Phase weg
    }
    
    public void testVacuous4(){
    	PhaseEventAutomata a1, a2,  aParallel;
    	a1 = patternToPEA.absencePattern(P.negate().and(Q.negate().and(R.negate().and(S.negate()))), Q, R, "Globally");
    	a2 = patternToPEA.precedencePattern(P, Q, R, S, "Between");
    	aParallel = a1.parallel(a2);
	    dotwriter.write("C:/vacuous/bsp4.dot", aParallel);
    }
    
    public void testVacuousProperty3(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata a1, a2, a3, aParallel;
    	
    	a1 = patternToPEA.invariantPattern(P, Q, R, S, "After");
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(Q),
	    	    new CounterTrace.DCPhase(),
	    	    new CounterTrace.DCPhase(P),
	    	    new CounterTrace.DCPhase()
	    	});
	    	a2 = compiler.compile("T1", ct); //ctA.dump();
    	
	    final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
		    	    new CounterTrace.DCPhase(),
		    	    new CounterTrace.DCPhase(Q),
		    	    new CounterTrace.DCPhase(),
		    	    new CounterTrace.DCPhase(S.negate()),
		    	    new CounterTrace.DCPhase()
		    	});
		a3 = compiler.compile("T2", ct2); //ctA.dump();
    	
    	aParallel = a3.parallel(a2);
	    dotwriter.write("C:/vacuous/vacuousProperty3_1.dot", a1);
	    dotwriter.write("C:/vacuous/vacuousProperty3_2.dot", a2);
	    dotwriter.write("C:/vacuous/vacuousProperty3_3.dot", a3);
	    dotwriter.write("C:/vacuous/vacuousProperty3_4.dot", aParallel);
    }
    
    //shows the subgraphs when building up a prefix of a requirement
    public void testVacuous(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata ctA, ctA2, ctA3;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P.and(S.negate())),
    			new CounterTrace.DCPhase(S.negate(), CounterTrace.BOUND_GREATER, 10),
    			new CounterTrace.DCPhase()
    	});
    	ctA = compiler.compile("1", ct);
    	
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P.and(S.negate())),
    			new CounterTrace.DCPhase(S.negate()),
    			new CounterTrace.DCPhase()
    	});
    	ctA2 = compiler.compile("2", ct2);
    	
    	final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P.and(S.negate())),
    			new CounterTrace.DCPhase()
    	});
    	ctA3 = compiler.compile("3", ct3);
    	
    	dotwriter.write("C:/vacuous/vaP_1.dot", ctA);
 	    dotwriter.write("C:/vacuous/vaP_2.dot", ctA2);
 	    dotwriter.write("C:/vacuous/vaP_3.dot", ctA3);

    }
    
  //shows the subgraphs when building up a prefix of a requirement
    public void testVacuous2(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata ctA, ctA2;
		final PhaseEventAutomata ctA3;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase(S),
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(T, CounterTrace.BOUND_GREATER, 10),
    			new CounterTrace.DCPhase()
    	});
    	ctA = compiler.compile("1", ct);
    	
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase(S),
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(T),
    			new CounterTrace.DCPhase()
    	});
    	ctA2 = compiler.compile("2", ct2);
    	
    	dotwriter.write("C:/vacuous/vaP2_1.dot", ctA);
 	    dotwriter.write("C:/vacuous/vaP2_2.dot", ctA2);

    }
    
  //shows the subgraphs when building up a prefix of a requirement
    public void testVacuous3(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata ctA, ctA2, ctA3;
//    	CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
//    			new CounterTrace.DCPhase(),
//    			new CounterTrace.DCPhase(P),
//    			new CounterTrace.DCPhase(T, CounterTrace.BOUND_GREATER, 10),
//    			new CounterTrace.DCPhase(CounterTrace.BOUND_GREATER, 10),
//    			new CounterTrace.DCPhase()
//    	});
    	//PhaseEventAutomata ctA, ctA2, ctA3;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase(CounterTrace.BOUND_LESS, 6),
    			new CounterTrace.DCPhase(Q),
    			new CounterTrace.DCPhase()
    	});
    	ctA = compiler.compile("1", ct);
    	
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase(T),
    			new CounterTrace.DCPhase()
    	});
    	ctA2 = compiler.compile("2", ct2);
    	
    	final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase()
    	});
    	ctA3 = compiler.compile("2", ct3);
    	
    	dotwriter.write("C:/vacuous/vaP3_1_Jochen.dot", ctA);
 	    dotwriter.write("C:/vacuous/vaP3_2.dot", ctA2);
 	    dotwriter.write("C:/vacuous/vaP3_3.dot", ctA3);

    }
  //shows the graphs for the case \neg(x;x;...;x\wedge y;true)
    public void testVacuous5(){
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata ctA, ctA2, ctA3;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase(T.and(S)),
    			new CounterTrace.DCPhase()
    	});
    	ctA = compiler.compile("1", ct);
    	
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase(T),
    			new CounterTrace.DCPhase()
    	});
    	ctA2 = compiler.compile("2", ct2);
    	
    	final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P),
    			new CounterTrace.DCPhase(S),
    			new CounterTrace.DCPhase()
    	});
    	ctA3 = compiler.compile("3", ct3);
    	
    	dotwriter.write("C:/vacuous/vaP5_1.dot", ctA);
 	    dotwriter.write("C:/vacuous/vaP5_2.dot", ctA2);
 	    dotwriter.write("C:/vacuous/vaP5_3.dot", ctA3);

    }
    
  //Pr�fe: Kann man ein Beispiel aufbauen, das einen ZenoRun zu einem Deadlock hat,
    //der dann von Uppaal nicht erkannt wird?
    public void testZeno(){
    	final CDD P = BooleanDecision.create("Signal_1");
    	final CDD Q = BooleanDecision.create("Signal_2");
    	
    	final Trace2PEACompiler compiler = new Trace2PEACompiler(ILogger.getLogger(""));
    	PhaseEventAutomata ctA, ctA2, ctA3;
    	final CounterTrace ct = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			//new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase(P, CounterTrace.BOUND_GREATEREQUAL, 6),
    			new CounterTrace.DCPhase()
    	});
    	ctA = compiler.compile("z1", ct);
    	
    	final CounterTrace ct2 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase(P, CounterTrace.BOUND_LESS, 10),
    			new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase()
    	});
    	ctA2 = compiler.compile("z2", ct2);
    	
    	final CounterTrace ct3 = new CounterTrace(new CounterTrace.DCPhase[] {
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(Q),
    			new CounterTrace.DCPhase(),
    			new CounterTrace.DCPhase(P.negate()),
    			new CounterTrace.DCPhase()
    	});
    	ctA3 = compiler.compile("z3", ct3);
    	
    	dotwriter.write("C:/vacuous/zeno_1.dot", ctA);
 	    dotwriter.write("C:/vacuous/zeno_2.dot", ctA2);
 	    dotwriter.write("C:/vacuous/zeno_3.dot", ctA3);
 	    
 	    //ctA=ctA.parallel(ctA2.parallel(ctA3));
 	   ctA=ctA.parallel(ctA3);
 	   dotwriter.write("C:/vacuous/zeno_123.dot", ctA);
 	    final J2UPPAALConverter converter = new J2UPPAALConverter();
 	    converter.writePEA2UppaalFile("C:/vacuous/zeno.xml", ctA);
 	    

    }
    

    
	
	public void run(){
		vacuousTest22();
		//consistencyTest();
		//testSeeping3();
		//testVacuous4();
		//vacuousTest3();
		//PhaseEventAutomata aParallel = this.testBndInvarianceVacuous();
	    //dotwriter.write("C:/vacuous/bsp5.dot", aParallel);
	    //testVacuousProperty3();
		
//	    testPrecedenceChainPattern12(P,Q,R,S,T);
//	    testMaxDurationPattern(P,Q,R,S,T);
//	    testMinDurationPattern(P,Q,R,S,T);
	    //testVacuous3();
	    testZeno();
	    
	    //this.testUniversalityPattern(P, Q, R);
	    //this.testUniversalityPattern(Q, Q, S.and(T));
	    
	    //Deadlockexample
	   // this.testUppaal();
//	    this.testDeadlock();
//	    CDD velocity = BooleanDecision.create("velocity<10");
//	    CDD standstill = BooleanDecision.create("standstill");
//	    this.testUppaal2();
//	    this.testBndRespPattern(velocity, Q, R, standstill);
//	    testVacuous5();
	    
	    
	}
	
	public static void main(final String[] args) {
		// TODO Auto-generated method stub
		new TestPatternToPEA().run();
	}

}
