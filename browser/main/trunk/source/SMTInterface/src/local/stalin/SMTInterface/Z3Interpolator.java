package local.stalin.SMTInterface;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;

import local.stalin.SMTInterface.z3interpol.AssertionInterpolationRule;
import local.stalin.SMTInterface.z3interpol.DefIntroInterpolationRule;
import local.stalin.SMTInterface.z3interpol.ElimInterpolationRule;
import local.stalin.SMTInterface.z3interpol.IInterpolationRule;
import local.stalin.SMTInterface.z3interpol.Interpolants;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder;
import local.stalin.SMTInterface.z3interpol.KeepInterpolationRule;
import local.stalin.SMTInterface.z3interpol.MPInterpolationRule;
import local.stalin.SMTInterface.z3interpol.MonotonicityInterpolationRule;
import local.stalin.SMTInterface.z3interpol.NNFInterpolationRule;
import local.stalin.SMTInterface.z3interpol.ResolutionInterpolationRule;
import local.stalin.SMTInterface.z3interpol.TInterpolationRule;
import local.stalin.SMTInterface.z3interpol.TautologieInterpolationRule;
import local.stalin.SMTInterface.z3interpol.TransInterpolationRule;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.nativez3.Z3ProofRule;

import org.apache.log4j.Logger;

public class Z3Interpolator {
//	private static Logger s_Logger = Logger.getRootLogger();

	// Sync these constants with Z3_decl_kind enum
	public final static int PR_TRUE = 0;
	public final static int PR_ASSERTED = 1;
	public final static int PR_GOAL = 2;
	public final static int PR_MODUS_PONENS = 3;
	public final static int PR_REFLEXIVITY = 4;
	public final static int PR_SYMMETRY = 5;
	public final static int PR_TRANSITIVITY = 6;
	public final static int PR_TRANSITIVITY_STAR = 7;
	public final static int PR_MONOTONICITY = 8;
	public final static int PR_QUANT_INTRO = 9;
	public final static int PR_DISTRIBUTIVITY = 10;
	public final static int PR_AND_ELIM = 11;
	public final static int PR_NOT_OR_ELIM = 12;
	public final static int PR_REWRITE = 13;
	public final static int PR_REWRITE_STAR = 14;
	public final static int PR_PULL_QUANT = 15;
	public final static int PR_PULL_QUANT_STAR = 16;
	public final static int PR_PUSH_QUANT = 17;
	public final static int PR_ELIM_UNUSED_VARS = 18;
	public final static int PR_DER = 19;
	public final static int PR_QUANT_INST = 20;
	public final static int PR_HYPOTHESIS = 21;
	public final static int PR_LEMMA = 22;
	public final static int PR_UNIT_RESOLUTION = 23;
	public final static int PR_IFF_TRUE = 24;
	public final static int PR_IFF_FALSE = 25;
	public final static int PR_COMMUTATIVITY = 26;
	public final static int PR_DEF_AXIOM = 27;
	public final static int PR_DEF_INTRO = 28;
	public final static int PR_APPLY_DEF = 29;
	public final static int PR_IFF_OEQ = 30;
	public final static int PR_NNF_POS = 31;
	public final static int PR_NNF_NEG = 32;
	public final static int PR_NNF_STAR = 33;
	public final static int PR_CNF_STAR = 34;
	public final static int PR_SKOLEMIZE = 35;
	public final static int PR_MODUS_PONENS_OEQ = 36;
	public final static int PR_TH_LEMMA = 37;
	
	Theory theory;
	Formula[] formulas;
	
	// sync this with PR_* fields...
	private IInterpolationRule[] mrules = new IInterpolationRule[PR_TH_LEMMA + 1];
	
	private final void loadrules() {
		IInterpolationRule rule = new TautologieInterpolationRule();
		rule.install(mrules);
		rule = new DefIntroInterpolationRule();
		rule.install(mrules);
		rule = new ElimInterpolationRule();
		rule.install(mrules);
		rule = new KeepInterpolationRule();
		rule.install(mrules);
		rule = new MonotonicityInterpolationRule();
		rule.install(mrules);
		rule = new MPInterpolationRule();
		rule.install(mrules);
		rule = new NNFInterpolationRule();
		rule.install(mrules);
		rule = new ResolutionInterpolationRule();
		rule.install(mrules);
		rule = new TransInterpolationRule();
		rule.install(mrules);
		rule = new TInterpolationRule();
		rule.install(mrules);
		rule = new AssertionInterpolationRule();
		rule.install(mrules);
	}
	
	public Z3Interpolator(Theory t, Formula[] fs) {
		theory = t;
		formulas = fs;
		loadrules();
	}

	public void dumpProblem(PrintWriter pw) {
		Formula total = Atom.TRUE;
		for (int i = 0; i < formulas.length; i++)
			formulas[i] = normalize(formulas[i]);
		for (Formula f : formulas)
			total = theory.and(total, f);
		theory.dumpBenchmark(pw, total);
	}

	private Formula normalize(Formula f) {
		// TODO Auto-generated method stub
		return f;
	}
	
	class Node {
	}

	HashMap<Integer, Node> nodeMap;
	
	public Formula[] parseAndInterpolate(BufferedReader pr) {
		Node root;
		int lineNr = 0;
		try {
			/* skip first line reading 1:valid */
			pr.readLine();
			lineNr++;
			String nodedef;
			nodeMap = new HashMap<Integer, Node>();
			while (true)
			{
				nodedef = pr.readLine();
				lineNr++;
				if (nodedef == null) {
//					s_Logger.error("Did not find root node in Z3 proof tree");
					return null;
				}
				nodedef = nodedef.trim();
				int idx = nodedef.indexOf(" := ");
				if (idx == -1) {
					root = parseRightHandSide(nodedef);
					break;
				} else {
					Node n = parseRightHandSide(nodedef.substring(idx+4));
					Integer i = parseNumber(nodedef.substring(0, idx));
					nodeMap.put(i, n);
				}
			}
		} catch (IOException ex) {
//			s_Logger.error("Cannot read output from Z3", ex);
		} finally {
			nodeMap = null;
		}
		// TODO Auto-generated method stub
		return null;
	}

	private int parseNumber(String number) {
		if (number.startsWith("#")) {
			return Integer.parseInt(number.substring(1));
		}
		// FIXME better exception handling.
		throw new IllegalArgumentException("Tree malformed: "+number);
	}

	private Node parseRightHandSide(String nodedef) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Interpolants interpolateRule(int rulenum,Formula[] antecedents,Interpolants[] antips,
			Formula res,InterpolationInfoHolder iih) throws InterpolationException {
		IInterpolationRule iir = mrules[rulenum];
		assert(checkAIPs(antips));
		if( iir == null )
			throw new InterpolationInfoHolder.InterpolationException("Rule not implemented: " + rulenum + "! Use PROOF_MODE=2 to get rid of _STAR rules");
		return iir.interpolate(formulas.length - 1, rulenum, antecedents, antips, res, iih);
	}
	
	private boolean checkAIPs(Interpolants[] aips) {
		for( Interpolants aip : aips )
			if( aip.getSize() != formulas.length -1)
				return false;
		return true;
	}
	
}
