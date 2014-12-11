package de.uni_freiburg.informatik.ultimatetest.knownbugs;

public class WitnessBugs extends AbstractBugTestSuite {

	@Override
	protected void fillTestCases() {
//		addAutomizer32bitPrecise("examples/svcomp/ldv-regression/test_while_int.c_false-unreach-call.i");
		
//		addAutomizer32bitPrecise("examples/svcomp/ldv-regression/test21_false-unreach-call.c");
		
		
		addAutomizer32bitPrecise("examples/svcomp/loops/sum03_false-unreach-call_true-termination.i");
		addAutomizer32bitPrecise("examples/svcomp/loops/verisec_OpenSER__cases1_stripFullBoth_arr_false-unreach-call.i");
		addAutomizer32bitPrecise("examples/svcomp/loops/eureka_01_false-unreach-call.i");
		addAutomizer32bitPrecise("examples/svcomp/loops/sum_array_false-unreach-call.i");
		addAutomizer32bitPrecise("examples/svcomp/loops/verisec_sendmail__tTflag_arr_one_loop_false-unreach-call.i");
		addAutomizer32bitPrecise("examples/svcomp/loops/vogal_false-unreach-call.i");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.3.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.4.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.3.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.4.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.BOUNDED-10.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.BOUNDED-10.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addAutomizer32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.01_false-unreach-call.i.cil.c");
		addAutomizer32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.07_false-unreach-call.i.cil.c");
		addAutomizer32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.09_false-unreach-call.i.cil.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem10_label42_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem11_label39_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label22_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label29_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label31_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label37_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label52_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label54_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label58_false-unreach-call.c");
		addAutomizer32bitPrecise("examples/svcomp/eca-rers2012/Problem18_label27_false-unreach-call.c");

		addImpulse32bitPrecise("examples/svcomp/ldv-regression/test_while_int.c_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/loops/sum03_false-unreach-call_true-termination.i");
		addImpulse32bitPrecise("examples/svcomp/loops/verisec_OpenSER__cases1_stripFullBoth_arr_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/loops/eureka_01_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/loops/sum_array_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/loops/verisec_sendmail__tTflag_arr_one_loop_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/loops/vogal_false-unreach-call.i");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.3.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_floodmax.3_false-unreach-call.4.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.3.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_opt-floodmax.3_false-unreach-call.4.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.BOUNDED-10.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.BOUNDED-10.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr-var-start-time.3_false-unreach-call.2.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/seq-mthreaded/pals_lcr.3_false-unreach-call.1.ufo.BOUNDED-6.pals.c");
		addImpulse32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.01_false-unreach-call.i.cil.c");
		addImpulse32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.07_false-unreach-call.i.cil.c");
		addImpulse32bitPrecise("examples/svcomp/ssh/s3_srvr.blast.09_false-unreach-call.i.cil.c");
		
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem11_label39_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label22_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label29_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label31_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label37_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label52_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label54_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem14_label58_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem18_label27_false-unreach-call.c");
		addImpulse32bitPrecise("examples/svcomp/eca-rers2012/Problem10_label42_false-unreach-call.c");
	}
	
	@Override
	protected int getTimeout() {
		//default: 300 * 1000
		return super.getTimeout();
	}

	private void addAutomizer32bitPrecise(String file) {
		addTestCase("AutomizerC.xml", "witness/svComp-32bit-precise-Automizer-Witness.epf", file);
	}

	private void addImpulse32bitPrecise(String file) {
		addTestCase("CodeCheckWithBE-C.xml", "witness/svComp-32bit-precise-BE-Impulse-Witness.epf", file);
	}
}
