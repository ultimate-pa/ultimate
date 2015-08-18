/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TermcompTests extends
		AbstractBuchiAutomizerTestSuite {
	
	
	private static final String[] m_UltimateRepository = {
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/AliasDarteFeautrierGonnord-SAS2010-speedpldi4_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/BradleyMannaSipma-CAV2005-Fig1_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/HarrisLalNoriRajamani-SAS2010-Fig1_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/HeizmannHoenickeLeikePodelski-ATVA2013-Fig7_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/Toulouse-BranchesToLoop_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/Toulouse-MultiBranchesToLoop_true-termination.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Termination_Category/gcd1_true-termination.c",
//		"examples/termination/termcomp2015/C/Ton_Chanh_15/Ackermann_true-termination.c",
//		"examples/termination/termcomp2015/C/Ultimate/Arrays03-ValueRestictsIndex_true-termination.c",
//		"examples/termination/termcomp2015/C/Ultimate/Bangalore_true-termination.c",
//		"examples/termination/termcomp2015/C/Ultimate/Gothenburg_true-termination.c",
//		"examples/termination/termcomp2015/C/Ultimate/Stockholm_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/AliasDarteFeautrierGonnord-SAS2010-speedFails4_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/AliasDarteFeautrierGonnord-SAS2010-speedpldi4_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/Bangalore_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/BradleyMannaSipma-CAV2005-Fig1_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/BrockschmidtCookFuhs-CAV2013-Fig9a_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/CookSeeZuleger-TACAS2013-Fig8b_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/Gothenburg_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/Stockholm_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/Toulouse-BranchesToLoop_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/Toulouse-MultiBranchesToLoop_true-termination.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/gcd1_true-termination.c",
//		"examples/termination/termcomp2015/C/AProVE_numeric/svcomp_Ackermann01_true-unreach-call_modified_modified.c",
//		"examples/termination/termcomp2015/C/AProVE_numeric/svcomp_b.03-no-inv_assume.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Mixed_Categories/Problem04_label00_true-unreach-call.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Mixed_Categories/s3_clnt_1_false-unreach-call.cil.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Mixed_Categories/splice_true-unreach-call.i",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/GCD3.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/PastaA9.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/PastaB3.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/svcomp_b.03-no-inv_assume.c",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15/svcomp_flag.c",
		
		
		
//		"examples/termination/termcomp2015/C/SV-COMP_Mixed_Categories/rekcba_aso_false-unreach-call.1.M1.c",
//		"examples/termination/termcomp2015/C/SV-COMP_Mixed_Categories/rekcba_ctm_false-unreach-call.2.c",
//		
		"examples/termination/termcomp2015/C/",
//		"examples/termination/termcomp2015/C_Integer/Stroeder_15",
//		"examples/termination/termcomp2015/C_Integer/Ton_Chanh_15",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 20 * 1000;
	}
	
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"buchiAutomizer/termcomp2015_Tests.epf",
//		"buchiAutomizer/termcomp2015_Tests_iZ3.epf",
	};
	
	
	private static final String[] m_CToolchains = {
		"AutomizerAndBuchiAutomizerCWithBlockEncoding.xml",
//		"BuchiAutomizerCWithBlockEncoding.xml",
//		"BuchiAutomizerCInlineWithBlockEncoding.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}
	
}
