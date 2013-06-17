package de.uni_freiburg.informatik.ultimate.boogie.cfg2smt;

//import java.io.FileNotFoundException;
import java.io.FileNotFoundException;
import java.util.List;
import java.util.ListIterator;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.Command;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.State;
import de.uni_freiburg.informatik.ultimate.boogie.cfg2smt.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.boogie.cfg2smt.Activator;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.Boogie2SMTAnnotation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGRootAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class CFG2SMTObserver implements IManagedObserver {
	
	private static final Boolean debugMessages = false;	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private Boogie2SMT boogie2smt;
	private Procedure lastProc = null;
	private Specification[] lastProcSpecs = null;
	
	//@Override
	public Command[] process(IPayload payload, State state, int childCount) {

		IAnnotations annotations = payload.getAnnotations().get("CFGBuilder"); 
		if (annotations == null){
			if(debugMessages)
				CFG2SMTObserver.s_Logger.info("No annotations in node!");
			return new Command[]{Command.DESCEND};
		}

		if (annotations instanceof CFGRootAnnotations) {
			CFGRootAnnotations rootAnnots = (CFGRootAnnotations) annotations;
			//Benchmark bm = new Benchmark(s_Logger);
			boogie2smt = new Boogie2SMT(makeBenchmark(),false, false);
			payload.getAnnotations().put("Boogie2SMT", new Boogie2SMTAnnotation(boogie2smt));
			
			List<Declaration> decls = rootAnnots.getDeclarations();
			for (Declaration decl : decls) {
				if (debugMessages)
					s_Logger.info("Processing " + decl);
				if (decl instanceof TypeDeclaration)
					boogie2smt.declareType((TypeDeclaration) decl); 
				else if (decl instanceof ConstDeclaration)
					boogie2smt.declareConstants((ConstDeclaration) decl); 
				else if (decl instanceof FunctionDeclaration)
					boogie2smt.declareFunction((FunctionDeclaration) decl); 
				else if (decl instanceof VariableDeclaration)
					boogie2smt.declareGlobalVariables((VariableDeclaration) decl);
				else if (decl instanceof Procedure)
					boogie2smt.declareProcedure((Procedure) decl);
				else
					throw new AssertionError("Unknown Declaration"+decl);
			}
			List<Axiom> axioms = (List<Axiom>) rootAnnots.getAxioms();
			for (Axiom ax : axioms) {
				if (debugMessages)
					s_Logger.info("Processing " + ax);
				boogie2smt.declareAxiom(ax);
			}
			rootAnnots.setScript(boogie2smt.getScript());
			return new Command[]{Command.DESCEND};
		}
		
		if(debugMessages) 
			CFG2SMTObserver.s_Logger.info("CurrentNode: " + payload.getName());

		if (annotations instanceof CFGNodeAnnotations) {
			CFGNodeAnnotations nodeAnnots = (CFGNodeAnnotations) annotations;
			
			if (nodeAnnots.isProcedureRoot()) {
				if (lastProc != null)
					boogie2smt.removeLocals(lastProc);
				Procedure proc = (Procedure) nodeAnnots.getProcedure();
				boogie2smt.declareLocals(proc);
				lastProc = proc;
				lastProcSpecs = boogie2smt.getProcedureSpecs(lastProc);
				processProcedure(payload);
			}
			processBlock(payload);
		}
		return new Command[]{Command.DESCEND};
	}

	private void processProcedure(IPayload payload){
		CFGNodeAnnotations annotations = 
			(CFGNodeAnnotations) payload.getAnnotations().get("CFGBuilder");
		for (Specification spec: lastProcSpecs){
			if (spec instanceof RequiresSpecification) {
				annotations.addStatement
					(0, new AssumeStatement(spec.getLocation(), ((RequiresSpecification) spec).getFormula()));
			}
		}
//		annotations.setOldVars(boogie2smt.getOldVars());
	}
	
	private void processBlock(IPayload payload){
		//boogie2smt.incGeneration();
		CFGNodeAnnotations annotation = 
			(CFGNodeAnnotations) payload.getAnnotations().get("CFGBuilder");
		
		List<Statement> statements = annotation.getStatements();
		
		boogie2smt.startBlock();
		boogie2smt.incGeneration();
		for (ListIterator<Statement> it = statements.listIterator(statements.size());
		     it.hasPrevious();) {
			Statement s = it.previous();
			if(debugMessages) CFG2SMTObserver.s_Logger.info("stmt: " + s.toString());

			if (s instanceof AssertStatement){
					boogie2smt.addAssert((AssertStatement) s);
			} else if (s instanceof AssumeStatement){
				boogie2smt.addAssume((AssumeStatement) s);
			} else if (s instanceof AssignmentStatement){
				boogie2smt.addAssignment((AssignmentStatement) s);
			} else if (s instanceof HavocStatement){
				boogie2smt.addHavoc((HavocStatement) s);
			} else if (s instanceof CallStatement){
				boogie2smt.addProcedureCall((CallStatement) s);
			} else if (s instanceof ReturnStatement){
				for (Specification spec: lastProcSpecs){
					if (spec instanceof EnsuresSpecification && !spec.isFree()) {
						boogie2smt.addAssert(new AssertStatement(spec.getLocation(), ((EnsuresSpecification) spec).getFormula()));
					}
				}
			} else {
				assert false : "Unknown Statement "+s;
			}
		}
		if (debugMessages) { 
			CFG2SMTObserver.s_Logger.info("CFG2SMT Assert: " + payload.getName()
					+ boogie2smt.getAsserts());
			CFG2SMTObserver.s_Logger.info("CFG2SMT Assume: " + payload.getName()
					+ boogie2smt.getAssumes());
		}
		annotation.setVars(boogie2smt.getAllVars());
		annotation.setInVars(boogie2smt.getInVars());
		annotation.setOutVars(boogie2smt.getOutVars());
		annotation.setAssertion(boogie2smt.getAsserts());
		annotation.setAssumption(boogie2smt.getAssumes());
		boogie2smt.endBlock();
	}
	
	
	private Script makeBenchmark() {
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		
//		int selectedSolver = Integer.valueOf(prefs.get(PreferenceValues.NAME_SELECTEDSOLVER,
//				PreferenceValues.VALUE_SELECTEDSOLVER_DEFAULT));
		
		String dumpPath = prefs.get(PreferenceValues.NAME_DUMPPATH, PreferenceValues.VALUE_DUMPPATH_DEFAULT);
		if (dumpPath != ""){
			dumpPath += (dumpPath.endsWith(System.getProperty("file.separator"))?"":System.getProperty("file.separator"));
		}
		
		Logger interpolLogger = Logger.getLogger("interpolLogger");
		interpolLogger.info("created new logger");
		interpolLogger.setLevel(Level.WARN);
		interpolLogger.info("Message not visible");
		Script m_Script = new SMTInterpol(interpolLogger);
		if (dumpPath != ""){
			try {
				dumpPath += (dumpPath.endsWith(System.getProperty("file.separator"))?"":System.getProperty("file.separator"));
				m_Script = new LoggingScript(m_Script, dumpPath + "dump.smt2", true);
				s_Logger.info("Writing smt2 log into file " + dumpPath + "dump.smt2");
			} catch (FileNotFoundException e) {
				throw new AssertionError(e);
			}
		}
		m_Script.setOption(":produce-models", true);
		m_Script.setOption(":produce-proofs", true);
		m_Script.setOption(":interpolant-check-mode", true);
		m_Script.setLogic("QF_UFLIRA");
		return m_Script;
	}
	
	//@Override
	public void finish() {
		if (lastProc != null)
			boogie2smt.removeLocals(lastProc);
	}

	//@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	//@Override
	public void init() {
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
