package local.stalin.SMTInterface.groundify;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.SMTInterface.preferences.nativez3.Z3ConfigConfigurator;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.nativez3.NativeCodeException;
import local.stalin.nativez3.Z3Config;
import local.stalin.nativez3.Z3Context;
import local.stalin.nativez3.Z3Exception;
import local.stalin.nativez3.Z3Parser;
import local.stalin.smt.convert.ConvertFormula;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.hack.GroundMap;
import local.stalin.smt.hack.Instantiation;
import local.stalin.smt.hack.SymbolRange;

import org.apache.log4j.Logger;

public class Groundifier {
	private static Logger s_logger = StalinServices.getInstance().getLoggerForExternalTool("Groundifier");
	private Theory mtheory;
	private Z3Context mctx;
	private RangeMap mrm;
	private Map<QuantifiedFormula,Map<TermVariable,Term>> skolems;
	private Map<QuantifiedFormula,Set<Instantiation>> inst;
	private QuantifierMarker mqm;
	
	public Groundifier(Theory theory) throws Z3Exception, NativeCodeException {
		mtheory = theory;
		Z3Config cfg = new Z3Config.Z3ConfigProof();
		Z3ConfigConfigurator.configure(cfg);
		mctx = new Z3Context(cfg,theory);
		// Allow VM to make space...
		cfg = null;
		mqm = new QuantifierMarker(theory);
		Z3Parser parser = mctx.getParser();
		FormulaUnFleterer unflet = new FormulaUnFleterer(mtheory);
		for( Formula ass : mtheory.getAxioms() ) {
			Formula fass = unflet.unflet(ass);
			parser.addAssumption(mqm.markQuantifiers(fass,-1));
		}
	}
	public Formula[] computeInterpolants(Formula[] forms) throws Z3Exception, NativeCodeException {
		Map<Integer,QFRange> allocnums = new HashMap<Integer,QFRange>();
		mrm = new RangeMap(mtheory);
		mqm.setAllocationMap(allocnums);
		mctx.push();
		Z3Parser parser = mctx.getParser();
		FormulaUnFleterer unflet = new FormulaUnFleterer(mtheory);
		for( Formula ass : mtheory.getAxioms() ) {
			Formula fass = unflet.unflet(ass);
			parser.addAssumption(mqm.markQuantifiers(fass,-1));
		}
		for( int i = 0; i < forms.length; ++i ) {
			forms[i] = unflet.unflet(forms[i]);
			Formula form = mqm.markQuantifiers(forms[i], i);
			parser.addAssumption(form);
		}
		Set<Formula> skolemforms = new HashSet<Formula>();
		Set<Formula> instforms = new HashSet<Formula>();
		int nativeres = mctx.checkAndGetSkolemsInsts(skolemforms, instforms);
		s_logger.info("Z3 result: " + Z3Context.resultToString(nativeres));
		if( nativeres != Z3Context.Z3UNSAT )
			return null;
//		Z3ProofRule proof = mctx.getProof();
		// Free some space
		mctx.pop(1);
//		mctx.clearProof();
		s_logger.info("Formula is unsat! Interpolating...");
		if (forms.length == 1)
			return new Formula[0];
		mrm.generateRanges(forms);
		Map<EqualsAtom,SymbolRange> auxeqs = new HashMap<EqualsAtom, SymbolRange>();
		InstantiationFinder instfinder = new InstantiationFinder(mtheory,allocnums,mrm,auxeqs);
		skolems = instfinder.findSkolemizations(skolemforms);
		inst = instfinder.findInstances(instforms);
//		skolems = instfinder.findSkolemizations(proof);
//		inst = instfinder.findInstances(proof);
		
//		for (Formula f : skolemforms)
//			System.err.println(f);
//		for (Formula f : instforms)
//			System.err.println(f);
		
		// Release some memory...
//		proof = null;
		mtheory.clearTemps();
		mrm = null;
		allocnums = null;
		
		s_logger.debug("Found following skolemizations:");
		for( Map.Entry<QuantifiedFormula,Map<TermVariable,Term>> me : skolems.entrySet() ) {
			s_logger.debug("For " + me.getKey() + ":");
			Map<TermVariable,Term> skol = me.getValue();
			for (Map.Entry<TermVariable, Term> sme : skol.entrySet()) {
				s_logger.debug(sme.getKey() + " => " + sme.getValue());
			}
		}
		s_logger.debug("Found following instantiations:");
		for( Map.Entry<QuantifiedFormula,Set<Instantiation>> me : inst.entrySet() ) {
			s_logger.debug(me.getKey() + " ==> ");
			for( Instantiation ground : me.getValue() )
				s_logger.debug(ground);
		}
		GroundMap.singletonGroundMap().setSkolemMap(skolems);
		GroundMap.singletonGroundMap().setInstantiationMap(inst);
		GroundMap.singletonGroundMap().setLocalityMap(instfinder.getLocalityMap());
		GroundMap.singletonGroundMap().setAuxEqs(auxeqs);
		DPLLEngine engine = new DPLLEngine(mtheory,s_logger);
		ConvertFormula conv = new ConvertFormula(engine);
		engine.setInstantiationMap(instfinder.getLocalityMap());
		engine.setInferenceOrder(instfinder.getOrderMap());
		
		// Release some memory
		instfinder = null;
		
		for( Formula ass : mtheory.getAxioms() ) {
			Formula fass = unflet.unflet(ass);
			conv.addFormula(fass,forms.length-1);
		}
		for( Formula f : forms ) {
			Formula fform = f;//unflet.unflet(f);
			conv.addFormula(fform);
		}
		conv.addFormula(forms[forms.length-1], forms.length-1);
		conv.close();
//		engine.dumpClausesSMTLIB();
//		System.exit(0);
		if( engine.solve() )
			throw new AssertionError("Z3 says unsat, SmtInterpol says sat!");
		// Throw away temporary skolem constants
		mtheory.clearTemps();
		return engine.getInterpolants();
	}
	public Set<Instantiation> getInstantiations(QuantifiedFormula qf) {
		return inst.get(qf);
	}
	public Map<TermVariable,Term> getSkolemization(QuantifiedFormula qf) {
		return skolems.get(qf);
	}
}
