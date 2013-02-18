package local.stalin.boogie.cfg2smt;

import java.util.List;
import java.util.ListIterator;

import org.apache.log4j.Logger;

import local.stalin.access.IManagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.access.WalkerOptions.Command;
import local.stalin.access.WalkerOptions.State;
import local.stalin.boogie.cfgbuilder.Activator;
import local.stalin.boogie.cfgbuilder.CFGNodeAnnotations;
import local.stalin.boogie.cfgbuilder.CFGRootAnnotations;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IAnnotations;
import local.stalin.model.IPayload;
import local.stalin.model.boogie.ast.AssertStatement;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.EnsuresSpecification;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.RequiresSpecification;
import local.stalin.model.boogie.ast.ReturnStatement;
import local.stalin.model.boogie.ast.Specification;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.VariableDeclaration;

public class CFG2SMTObserver implements IManagedObserver {
	
	private static final Boolean debugMessages = false;	
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
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
			boogie2smt = new Boogie2SMT();
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
					boogie2smt.declareVariables((VariableDeclaration) decl);
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
			rootAnnots.setTheory(boogie2smt.getTheory());
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
					(0, new AssumeStatement(spec.getFilename(), spec.getLineNr(), ((RequiresSpecification) spec).getFormula()));
			}
		}
		annotations.setOldVars(boogie2smt.getOldVars());
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
						boogie2smt.addAssert(new AssertStatement(spec.getFilename(), spec.getLineNr(), ((EnsuresSpecification) spec).getFormula()));
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
