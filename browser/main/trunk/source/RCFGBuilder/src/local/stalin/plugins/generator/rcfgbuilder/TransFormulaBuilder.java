package local.stalin.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import local.stalin.boogie.cfg2smt.Boogie2SMT;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.VariableDeclaration;

/**
 * Provides methods to build TransitionsFormulas for the nodes and edges of a
 * recursive control flow graph.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TransFormulaBuilder {
	
	//We use Boogie2SMT to translate boogie Statements to SMT formulas 
	Boogie2SMT m_Boogie2smt = new Boogie2SMT();

	/**
	 * Add TransitionFormulas to all elements of a recursive control flow graph.
	 * @param The (unique) root node of a recursive control flow graph.
	 */
	public void addTransitionFormulasToRCFG(RootNode root) {
		
		//Get Declarations and Axioms of the program from the RootNode
		List<Declaration> decls = root.getRootAnnot().getDeclarations();
		List<Axiom> axioms = root.getRootAnnot().getAxioms();

		//Give all informations of Declarations and Axioms to Boogie2SMT
		for (Declaration decl : decls) {
			if (decl instanceof TypeDeclaration)
				m_Boogie2smt.declareType((TypeDeclaration) decl); 
			else if (decl instanceof ConstDeclaration)
				m_Boogie2smt.declareConstants((ConstDeclaration) decl); 
			else if (decl instanceof FunctionDeclaration)
				m_Boogie2smt.declareFunction((FunctionDeclaration) decl); 
			else if (decl instanceof VariableDeclaration)
				m_Boogie2smt.declareVariables((VariableDeclaration) decl);
			else if (decl instanceof Procedure) {
				//do nothing
			}
			else
				throw new AssertionError("Unknown Declaration"+decl);
		}
		for (Axiom ax : axioms) {
			m_Boogie2smt.declareAxiom(ax);
		}
		
		//We have to do this after declaring axioms, because some axioms
		//use variable identifiers that are also used for local variables.
		Map<String, Procedure> procs = root.getRootAnnot().getProcedures();
		Map<String, Procedure> impls = root.getRootAnnot().getImplementations();
		Set<Procedure> allProc = new HashSet<Procedure>();
		for (String procName : procs.keySet()) {
			allProc.add(procs.get(procName));
			m_Boogie2smt.declareProcedure(procs.get(procName));
		}
		for (String procName : impls.keySet()) {
			allProc.add(impls.get(procName));
		}
		for (Procedure proc : allProc) {
			m_Boogie2smt.declareLocalsFPWOWI(proc);
		}
		root.getRootAnnot().setTheory(m_Boogie2smt.getTheory());
		
		//Traverse the RCFG and add TransitionFormulas to all elements 
		List<LocNode> queue = new LinkedList<LocNode>();
		Set<LocNode> visited = new HashSet<LocNode>();
		for (INode succNode : root.getOutgoingNodes()) {
			queue.add((LocNode)succNode);
			visited.add((LocNode)succNode);
		}
		while (!queue.isEmpty()) {
			LocNode locNode = queue.remove(0);
			for (IEdge edge : locNode.getOutgoingEdges()) {
				addTransitionFormulas(edge);
			}
			if (locNode.getOutgoingNodes() != null) {
				for (INode succNode : locNode.getOutgoingNodes()) {
					if (!visited.contains(succNode)) {
						queue.add((LocNode)succNode);
						visited.add((LocNode)succNode);
					}
				}
			}
		}
	}
	
	/**
	 * Add TransitionFormulas to an edge in the recursive control flow graph. If
	 * the edge is a CallEdge or ReturnEdge two formulas are added. One that
	 * represents the local variable assignments one that represents the global
	 * variable assignments. If the edge is an InternalEdge one 
	 * TransitionFormula is added. This TransitionFormula represents the effect
	 * of all Assignment, Assume and Havoc Statements of this edge. If the edge
	 * is a GotoEdge or a SummaryEdge no TransitionFormula is added. 
	 * @param edge An IEdge that has to be a CallEdge, InternalEdge, ReturnEdge,
	 *  GotoEdge or SummaryEdge.
	 */
	private void addTransitionFormulas(IEdge edge) {
		if (edge instanceof InternalEdge || edge instanceof ReturnEdge) {
			TransAnnot transAnnot = (TransAnnot) 
					edge.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
			transAnnot.setTransitionFormula(
					getTransitionFormula(transAnnot.getStatements()));
					
		}
		else if (edge instanceof CallEdge) {
			CallAnnot callAnnot = ((CallEdge)edge).getCallAnnotations(); 
			edge.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
			callAnnot.setTransitionFormula(
					getTransitionFormula(callAnnot.getStatements()));
			callAnnot.setOldVarsEquality(
					getTransitionFormula(callAnnot.getGlobalVarSelfAssignment()));
		}
		else if (edge instanceof GotoEdge) {
			throw new IllegalArgumentException("Auxiliary Gotos should have" +
					"been removed.");
		}
		else if (edge instanceof SummaryEdge) {
			SummaryEdge summary = (SummaryEdge) edge;
			CallStatement st = summary.getCallStatement();
			TransAnnot transAnnot = (TransAnnot) 
					edge.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
			transAnnot.setTransitionFormula(getTransitionFormula(st));

		}
		else {
			throw new IllegalArgumentException();
		}
	}

	
	
	/**
	 * @return TransitionFormula that represents the effect of the input st.
	 */
	private TransFormula getTransitionFormula(AssignmentStatement st) {
		m_Boogie2smt.startBlock();
		m_Boogie2smt.addAssignment(st);
		TransFormula locVarAssignFormula = 
			new TransFormula(m_Boogie2smt.getAssumes(),
					m_Boogie2smt.getInVars(),
					m_Boogie2smt.getOutVars(),
					m_Boogie2smt.getOldVars(),
					m_Boogie2smt.getAllVars());
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return locVarAssignFormula;
	}
	
	/**
	 * @return TransitionFormula that represents the effect of the input st.
	 */
	private TransFormula getTransitionFormula(AssumeStatement st) {
		m_Boogie2smt.startBlock();
		m_Boogie2smt.addAssume(st);
		TransFormula locVarAssignFormula = 
			new TransFormula(m_Boogie2smt.getAssumes(),
					m_Boogie2smt.getInVars(),
					m_Boogie2smt.getOutVars(),
					m_Boogie2smt.getOldVars(),
					m_Boogie2smt.getAllVars());
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return locVarAssignFormula;
	}
	
	
	/**
	 * @return TransitionFormula that represents the effect of the input st.
	 */
	private TransFormula getTransitionFormula(CallStatement st) {
		m_Boogie2smt.startBlock();
		m_Boogie2smt.addProcedureCall(st);
		TransFormula locVarAssignFormula = 
			new TransFormula(m_Boogie2smt.getAssumes(),
					m_Boogie2smt.getInVars(),
					m_Boogie2smt.getOutVars(),
					m_Boogie2smt.getOldVars(),
					m_Boogie2smt.getAllVars());
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return locVarAssignFormula;
	}
	
	
	/**
	 * @param stmts List of Statements which may only be of type Assume,
	 * 	Assignment or Havoc Statement. 
	 * @return TransitionFormula that represents the effect of all input
	 *  Statements executed in a row.
	 */
	private TransFormula getTransitionFormula(List<Statement> stmts) {
		m_Boogie2smt.startBlock();
		m_Boogie2smt.incGeneration();
		
		for (ListIterator<Statement> it = stmts.listIterator(stmts.size());
	     it.hasPrevious();) {
		Statement st = it.previous();
		if (st instanceof AssumeStatement){
			m_Boogie2smt.addAssume((AssumeStatement) st);
		} else if (st instanceof AssignmentStatement){
			m_Boogie2smt.addAssignment((AssignmentStatement) st);
		} else if (st instanceof HavocStatement){
			m_Boogie2smt.addHavoc((HavocStatement) st);
		} else {
			throw new IllegalArgumentException("Intenal Edge only contains" +
					" Assume, Assignment or Havoc Statement");
		}
	}
		TransFormula locVarAssignFormula = 
			new TransFormula(m_Boogie2smt.getAssumes(),
					m_Boogie2smt.getInVars(),
					m_Boogie2smt.getOutVars(),
					m_Boogie2smt.getOldVars(),
					m_Boogie2smt.getAllVars());
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return locVarAssignFormula;
	}

}
