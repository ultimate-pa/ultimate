package local.stalin.SMTInterface;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.Set;

import local.stalin.SMTInterface.groundify.Groundifier;
import local.stalin.SMTInterface.preferences.PreferenceValues;
import local.stalin.SMTInterface.preferences.nativez3.Z3ConfigConfigurator;
import local.stalin.SMTInterface.z3interpol.Interpolants;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder;
import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.toolchain.IStorable;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.Sort;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.nativez3.NativeCodeException;
import local.stalin.nativez3.Z3Config;
import local.stalin.nativez3.Z3Context;
import local.stalin.nativez3.Z3Exception;
import local.stalin.nativez3.Z3Parser;
import local.stalin.nativez3.Z3ProofRule;
import local.stalin.smt.convert.ConvertFormula;
import local.stalin.smt.dpll.DPLLEngine;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

public class SMTInterface implements IStorable {
	private static Logger s_Logger = StalinServices.getInstance().getLoggerForExternalTool("SMTInterface");
	
	public static final int SMT_UNSAT = 0;
	public static final int SMT_SAT = 1;
	public static final int SMT_UNKNOWN = 2;
	public static final int SMT_ERROR = -1;
	
	public static final int SOLVER_SMTLIB = 0;
	public static final int SOLVER_SMTINTERPOL = 1;
	public static final int SOLVER_Z3_SIMPLIFY = 2;
	public static final int SOLVER_Z3_NATIVE = 3;
	public static final int SOLVER_Z3_NATIVE_INTERPOL = 4;
	public static final int SOLVER_GROUNDIFY = 5;// Z3Native for check
	
	Theory theory;
	private int ctr;
	int solver;
	private PrintWriter engineInput;
	private BufferedReader engineOutput;
	private BufferedReader engineError;
	private SimplifyOutput simplifyOutput;
	private Process p;
	private Z3Context ctx;
	private Groundifier ground;
	
	
	/**
	 * Creates an instance of this class for a given theory.  The theory must
	 * not be changed after this class was created, i.e. no new function symbols
	 * and axioms may be added.
	 * You can use this instance to call smtCheck for several formulas, using the
	 * same axioms.
	 * 
	 * @param t   The theory, containing all axioms needed for the prover.
	 *            
	 */
	public SMTInterface(Theory t) {
		this(t, SOLVER_Z3_SIMPLIFY);
	}
	
	/**
	 * Creates an instance of this class for a given theory.  The theory must
	 * not be changed after this class was created, i.e. no new function symbols
	 * and axioms may be added.
	 * You can use this instance to call smtCheck for several formulas, using the
	 * same axioms.
	 * 
	 * @param t   The theory, containing all axioms needed for the prover.
	 *            
	 */
	public SMTInterface(Theory t, int solver) {
		this.theory = t;
		this.solver = solver;
		
		if (solver == SOLVER_Z3_SIMPLIFY) {
			initializeSolverZ3Simplify();
		} else if( solver >= SOLVER_Z3_NATIVE && solver != SOLVER_GROUNDIFY ) {
			initializeSolverZ3Native();
		} else if (solver == SOLVER_GROUNDIFY)
			try {
				ground = new Groundifier(theory);
			} catch (Z3Exception e) {
				throw new RuntimeException(e);
			} catch (NativeCodeException e) {
				throw new RuntimeException(e);
			}
	}
	
	private void initializeSolverZ3Native() {
		try {
			// I rely on this assumption: solver != SOLVER_Z3_NATIVE means "we want the proof tree"
			Z3Config cfg = solver == SOLVER_Z3_NATIVE ? new Z3Config() : new Z3Config.Z3ConfigProof();
			Z3ConfigConfigurator.configure(cfg);
			ctx = new Z3Context(cfg,theory);
			// Allow VM to make space...
			cfg = null;
			// Add all axioms
			Z3Parser parser = ctx.getParser();
			for( Formula a : theory.getAxioms() )
				parser.addAssumption(a);
		} catch( Z3Exception exc ) {
			s_Logger.fatal("Could not create native Z3 solver", exc);
		} catch( NativeCodeException nce ) {
			s_Logger.fatal("Could not create native Z3 solver", nce);
		}
	}

	public void close() {
		if (solver == SOLVER_Z3_SIMPLIFY) {
			try {
				engineInput.close();
				engineOutput.close();
				engineError.close();
				p.destroy();
			} catch (IOException e) {
				s_Logger.error("Exception in communication with SMT solver", e);
			}
		} else if( solver >= SOLVER_Z3_NATIVE ) {
			ctx = null;
		}
	}

	private void initializeSolverZ3Simplify() {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);

		try {
			p = Runtime.getRuntime().exec(
					prefs.get(PreferenceValues.NAME_SMTEXECUTABLE,PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT)
					+ " " 
					+ prefs.get(PreferenceValues.NAME_SMTPARAMETER,PreferenceValues.VALUE_SMTPARAMETER_DEFAULT)
					+ " "
					+ prefs.get(PreferenceValues.NAME_OPTION_PREFIX, PreferenceValues.VALUE_OPTION_PREFIX_DEFAULT)
					+ "si"
				);
			
			s_Logger.info("SMT Output");
			engineInput  = new PrintWriter(new OutputStreamWriter(p.getOutputStream()));
			engineOutput = new BufferedReader(new InputStreamReader(p.getInputStream()));
			engineError  = new BufferedReader(new InputStreamReader(p.getErrorStream()));
			
			simplifyOutput = new SimplifyOutput(engineInput);
			simplifyOutput.dumpTheory(theory);
		} catch (IOException e) {
			s_Logger.error("Exception in communication with SMT solver", e);
		}
	}
	
	/**
	 * Checks if the formula f is satisfiable.
	 * The function will call dumpBenchmark of the Theory to produce a file in
	 * SMT format. This file will then be transfered to an external SMT solver
	 * (standard is Z3, which is part of the VCC distribution). There exists
	 * a preference page where alternatives can be inserted. The result is an
	 * integer telling whether the formula was satisfiable, unsatisfiable,
	 * unknown, or an error (parse errors etc.).
	 * 
	 * @param f   The formula to be sent to the SMT solver.
	 * @Theory t
	 *            The theory, containing all axioms needed for the prover.
	 * @return
	 * 			  The result will be one of the constants, defined above.
	 *            It will also throw an exception if an error occurs.
	 *            
	 */
	public int checkSatisfiable(Formula f) {
		if (solver == SOLVER_SMTLIB)
			return checkSatisfiabilitySmtlib(f);
		else if (solver == SOLVER_Z3_SIMPLIFY)
			return checkSatisfiabilityZ3Simplify(f);
		else if (solver == SOLVER_GROUNDIFY)
			return checkSatisfiabilityGroundify(f);
		else if (solver >= SOLVER_Z3_NATIVE)
			return checkSatisfiabilityZ3Native(f);
		else {
			return checkSatisfiabilitySmtInterpol(f);
		}
	}
		
	private int checkSatisfiabilityGroundify(Formula f) {
		try {
			Z3Config cfg = new Z3Config();
			Z3ConfigConfigurator.configure(cfg);
			Z3Context curctx = new Z3Context(cfg,theory);
			// Allow VM to make space...
			cfg = null;
			// Add all axioms
			Z3Parser parser = curctx.getParser();
			for( Formula a : theory.getAxioms() )
				parser.addAssumption(a);
			curctx.push();
			parser.addAssumption(f);
			int nativeres = curctx.check();
			curctx.pop(1);
			switch( nativeres ) {
				case Z3Context.Z3SAT:
					return SMT_SAT;
				case Z3Context.Z3UNSAT:
					return SMT_UNSAT;
				case Z3Context.Z3UNKNOWN:
					return SMT_UNKNOWN;
			}
		} catch( Z3Exception exc ) {
			s_Logger.fatal("Failed to check satisfiability!", exc);
			return SMT_ERROR;
		} catch( NativeCodeException nce ) {
			s_Logger.fatal("Failed to check satisfiability!", nce);
			return SMT_ERROR;
		}
		return SMT_ERROR;
	}

	private int checkSatisfiabilityZ3Native(Formula f) {
		try {
			ctx.push();
			ctx.getParser().addAssumption(f);
			int nativeres = ctx.checkAndGetProof();
			ctx.pop(1);
			switch( nativeres ) {
				case Z3Context.Z3SAT:
					return SMT_SAT;
				case Z3Context.Z3UNSAT:
					return SMT_UNSAT;
				case Z3Context.Z3UNKNOWN:
					return SMT_UNKNOWN;
			}
		} catch( Z3Exception exc ) {
			s_Logger.fatal("Failed to check satisfiability!", exc);
			return SMT_ERROR;
		} catch( NativeCodeException nce ) {
			s_Logger.fatal("Failed to check satisfiability!", nce);
			return SMT_ERROR;
		}
		return SMT_ERROR;
	}

	private int checkSatisfiabilitySmtlib(Formula f) {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);

		FileWriter file;
		File smtfile = null;
		boolean remove = 
			!prefs.getBoolean(PreferenceValues.NAME_SAVESMTLIBFILES,
				PreferenceValues.VALUE_SAVESMTLIBFILES);
		try {
			String filename = 
				prefs.get(
				PreferenceValues.NAME_TEMPPATH,
				PreferenceValues.VALUE_TEMPPATH_DEFAULT) //+ File.separatorChar
				+ "test" + (ctr++) + ".smt";
			smtfile = new File(filename);
			if (remove)
				smtfile.deleteOnExit();
			file = new FileWriter( smtfile );
			PrintWriter pw = new PrintWriter(file);
			theory.dumpBenchmark(pw, f);
			pw.flush();
			pw.close();
			
			s_Logger.info(filename);
			
			//---------------------------------------------------------------------------------------
			//Fixes problem with whitespaces in path
			
			String[] cmd = {prefs.get(PreferenceValues.NAME_SMTEXECUTABLE,PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT),
					prefs.get(PreferenceValues.NAME_SMTPARAMETER,PreferenceValues.VALUE_SMTPARAMETER_DEFAULT),
					filename};
			Process p = Runtime.getRuntime().exec(cmd);
			//---------------------------------------------------------------------------------------
			
			/*Process p = Runtime.getRuntime().exec(
					prefs.get(PreferenceValues.NAME_SMTEXECUTABLE,PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT)
					+ " " 
					+ prefs.get(PreferenceValues.NAME_SMTPARAMETER,PreferenceValues.VALUE_SMTPARAMETER_DEFAULT)
					+ " "
					+ filename
				);*/
			
			s_Logger.info("SMT Output");
			BufferedReader pr = new BufferedReader(new InputStreamReader(p.getInputStream()));
			BufferedReader error = new BufferedReader(new InputStreamReader(p.getErrorStream()));
			String x1;
			while ((x1 = error.readLine()) != null)
			{
				if (x1.contains("WARNING")) { s_Logger.warn(x1); } else s_Logger.error(x1);
				if (x1.contains("ERROR")) { throw(new NullPointerException(x1));}
			}
			while ((x1 = pr.readLine()) != null)
			{
				s_Logger.info(x1);
				if (x1.equals("unknown")) { return SMT_UNKNOWN; }
				if (x1.equals("unsat")) { return SMT_UNSAT; }
				if (x1.equals("sat")) { return SMT_SAT; }
			}
			// I guess this is a kill
			if (p.exitValue() != 0)
				return SMT_UNKNOWN;
		} catch (IOException e) {
			s_Logger.error("Exception in communication with SMT solver", e);
		} finally {
			if (remove && smtfile != null) {
				smtfile.delete();// Don't care about the result of this
			}
		}
		return SMT_ERROR;
	}
	
	private int checkSatisfiabilityZ3Simplify(Formula f) {
		int result = SMT_ERROR;
		try {
			s_Logger.info("checking formula via Z3 simplify interactive mode");
			simplifyOutput.checkFormula(theory.not(f));
			engineInput.flush();
			String line;
			while ((line = engineOutput.readLine()) != null)
			{
				s_Logger.info(line);
				if (line.contains(": Invalid"))
					result = SMT_SAT;
				else if (line.contains(": Valid"))
					result = SMT_UNSAT;
				//if (line.charAt(line.length()-1) == '.')
				else if (line.contains("ERROR:")) {
					s_Logger.error(line);
					result = SMT_ERROR;
					break;
				}
				else if (line.contains("WARNING:"))
					s_Logger.warn(line);
				if (line.equals(".") || (Character.isDigit(line.charAt(0)) && line.charAt(line.length()-1) == '.')) {
					break;
				}
			}
		} catch (IOException e) {
			s_Logger.error("Exception in communication with SMT solver", e);
		}
		return result;
	}
	
	private int checkSatisfiabilitySmtInterpol(Formula f) {
		Logger dplllogger = 
			StalinServices.getInstance().getLoggerForExternalTool("SmtInterpol");
		DPLLEngine engine = new DPLLEngine(theory,dplllogger);
		ConvertFormula converter = new ConvertFormula(engine);
		converter.addFormula(f);
		converter.close();
		if (engine.solve())
			return SMT_SAT;
		else
			return SMT_UNSAT;
	}

	/**
	 * Compute interpolants for a sequence of formulas.  
	 * @param fs A sequence of formulas of length n such that 
	 *        <code>fs[0] && ... && fs[n-1] ==&gt; FALSE</code>
	 * @param vs The free variables that appear in the formulas.
	 * @return A sequence of formulas of length n-1 such that
	 *        <ul><li>fs[0] ==&gt; result[0]</li>
	 *        	  <li>result[i] && fs[i+1] ==&gt; result[i+1], for i=0,...,n-3</li>
	 *        	  <li>result[n-2] && fs[n-1] ==&gt; FALSE</li>
	 *            <li>result[i] contains only variables that appear in one
	 *            	  result[j] with j&lt;=i and one result[j] with j &gt; i.</li>
	 *        </ul>
	 */
	public Formula[] computeInterpolants(Formula[] fs, Set<TermVariable> vars) {
		if (fs.length < 2)
			throw new IllegalArgumentException("WTF should I interpolate?");
		if (solver == SOLVER_SMTLIB)
			return computeInterpolantsSmtlib(fs, vars);
		else if( solver == SOLVER_Z3_NATIVE_INTERPOL )
			return computeInterpolantsNativeZ3(fs,vars);
		else if( solver == SOLVER_GROUNDIFY )
			return computeInterpolantsGroundify(fs,vars);
		else if (solver == SOLVER_SMTINTERPOL)
			return computeInterpolantsSMTInterpol(fs, vars);
		else if (solver == SOLVER_Z3_NATIVE){
			try {
				Z3Parser parser = ctx.getParser();
				ctx.push();
				FormulaUnFleterer unflet = new FormulaUnFleterer(theory);
				for (Formula f : fs)
					parser.addAssumption(unflet.unflet(f));
				int nativeres = ctx.check();
				ctx.pop(1);
				switch( nativeres ) {
					case Z3Context.Z3UNSAT:
						// Just a dummy for interpolant
						return new Formula[0];
					default:
						return null;
				}
			} catch( Z3Exception exc ) {
				s_Logger.fatal("Failed to check satisfiability!", exc);
			} catch( NativeCodeException nce ) {
				s_Logger.fatal("Failed to check satisfiability!", nce);
			}
		}
		throw new IllegalArgumentException("Cannot compute Interpolants using non-interpolating solver");
	}
	private Formula[] computeInterpolantsGroundify(Formula[] fs,
			Set<TermVariable> vars) {
		try {
			return ground.computeInterpolants(fs);
		} catch( Z3Exception exc ) {
			s_Logger.fatal("Failed to check satisfiability!", exc);
			throw new RuntimeException(exc);
		} catch( NativeCodeException nce ) {
			s_Logger.fatal("Failed to check satisfiability!", nce);
			throw new RuntimeException(nce);
		}
	}
	private static final Sort[] EMPTY_SORT_ARRAY = new Sort[0];
	private Formula[] computeInterpolantsNativeZ3(Formula[] fs,
			Set<TermVariable> vars) {
		try {
			ctx.push();
			Z3Parser parser = ctx.getParser();
			for( int i = 0; i < fs.length; ++i ) {
				Formula f = fs[i];
				fs[i] = theory.and(theory.atom(theory.createPredicate("ass"+i,EMPTY_SORT_ARRAY,true)),f);
				parser.addAssumption(fs[i]);
			}
			int nativeres = ctx.checkAndGetProof();
			ctx.pop(1);
			if( nativeres != Z3Context.Z3UNSAT )
				return null;
			Z3Interpolator interpol = new Z3Interpolator(theory,fs);
			InterpolationInfoHolder iih = new InterpolationInfoHolder(theory,fs);
			iih.update(ctx.getProof());
			return interpolateProof(interpol,ctx.getProof(),iih).getInterpolants();
		} catch( Z3Exception exc ) {
			s_Logger.fatal("Failed to check satisfiability!", exc);
		} catch( NativeCodeException nce ) {
			s_Logger.fatal("Failed to check satisfiability!", nce);
		} catch (InterpolationException e) {
			s_Logger.fatal("Exception during Z3 Interpolation", e);
		}
		return null;
	}
	
	private Interpolants interpolateProof(Z3Interpolator ip,Z3ProofRule pr,InterpolationInfoHolder iih) throws InterpolationException {
		Z3ProofRule[] antecedents = pr.getAntecedents();
		Formula[] fantecedents = new Formula[antecedents.length];
		Interpolants[] ips = new Interpolants[antecedents.length];
		for( int i = 0; i < antecedents.length; ++i ) {
			fantecedents[i] = antecedents[i].getResult();
			ips[i] = interpolateProof(ip,antecedents[i],iih);
			assert(ips[i] != null);
		}
		System.err.println("Interpolating rule " + pr.getRuleName());
		return ip.interpolateRule(pr.getRuleNumber(),fantecedents,ips,pr.getResult(),iih);
	}

	private Formula[] computeInterpolantsSMTInterpol(Formula[] fs, Set<TermVariable> vars) {
		Logger dplllogger = 
			StalinServices.getInstance().getLoggerForExternalTool("SmtInterpol");
		DPLLEngine engine = new DPLLEngine(theory,dplllogger);
		ConvertFormula converter = new ConvertFormula(engine);
		for (Formula f : fs)
			converter.addFormula(f);
		converter.close();
		if (!engine.solve()) {
			return engine.getInterpolants();
		}
		return null;
	}
	
	private Formula[] computeInterpolantsSmtlib(Formula[] fs, Set<TermVariable> vars) {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);

		FileWriter file;
		try {
			String filename = 
				prefs.get(
				PreferenceValues.NAME_TEMPPATH,
				PreferenceValues.VALUE_TEMPPATH_DEFAULT)
				+ "test.smt";
			file = new FileWriter( filename );
			PrintWriter pw = new PrintWriter(file);
			Z3Interpolator z3i = new Z3Interpolator(theory, fs);
			z3i.dumpProblem(pw);
			pw.flush();
			
			s_Logger.info(filename);
			
			Process p = Runtime.getRuntime().exec(
					prefs.get(PreferenceValues.NAME_SMTEXECUTABLE,PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT)
					+ " " 
					+ prefs.get(PreferenceValues.NAME_SMTPARAMETER,PreferenceValues.VALUE_SMTPARAMETER_DEFAULT)
					+ " "
					+ "PROOF_MODE=2 DISPLAY_PROOF=true "
					+ filename
				);
			
			s_Logger.info("SMT Output");
			BufferedReader pr = new BufferedReader(new InputStreamReader(p.getInputStream()));
			BufferedReader error = new BufferedReader(new InputStreamReader(p.getErrorStream()));
			String x1;
			while ((x1 = error.readLine()) != null)
			{
				if (x1.contains("WARNING")) { s_Logger.warn(x1); } else s_Logger.error(x1);
				if (x1.contains("ERROR")) { throw(new NullPointerException(x1));}
			}
			return z3i.parseAndInterpolate(pr);
		} catch (IOException e) {
			s_Logger.error("Exception in communication with SMT solver", e);
		}
		return null;
	}

	/**
	 * Checks if the formula f is satisfiable.
	 * The function will call dumpBenchmark of the Theory to produce a file in
	 * SMT format. This file will then be transfered to an external SMT solver
	 * (standard is Z3, which is part of the VCC distribution). There exists
	 * a preference page where alternatives can be inserted. The result is an
	 * integer telling whether the formula was satisfiable, unsatisfiable,
	 * unknown, or an error (parse errors etc.).
	 * 
	 * @param f   The formula to be sent to the SMT solver.
	 * @param t   The theory, containing all axioms needed for the prover.
	 * @return
	 * 			  The result will be one of the constants, defined above.
	 *            It will also throw an exception if an error occurs.
	 *            
	 */
	public static int SMTCall (Formula f, Theory t) {
		SMTInterface iface = new SMTInterface(t);
		int result = iface.checkSatisfiable(f);
		iface.close();
		return result;
	}
	public Z3ProofRule z3proof() {
		return ctx.getProof();
	}

	@Override
	public void destroy() {
		close();
	}
	public boolean isInterpolating() {
		return solver == SOLVER_SMTINTERPOL || solver == SOLVER_GROUNDIFY;
	}
}
