package local.stalin.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.boogie.type.BoogieType;
import local.stalin.boogie.type.PrimitiveType;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IEdge;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.model.Location;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.AssertStatement;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.BinaryExpression;
import local.stalin.model.boogie.ast.BooleanLiteral;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.EnsuresSpecification;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.GotoStatement;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.Label;
import local.stalin.model.boogie.ast.LoopInvariantSpecification;
import local.stalin.model.boogie.ast.ModifiesSpecification;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.RequiresSpecification;
import local.stalin.model.boogie.ast.ReturnStatement;
import local.stalin.model.boogie.ast.Specification;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.UnaryExpression;
import local.stalin.model.boogie.ast.Unit;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableDeclaration;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot.Origin;

import org.apache.log4j.Logger;

/**
 * This Plugin generates a recursive control flow graph (in the style of POPL'10
 * - Heizmann, Hoenicke, Podelski - Nested Interpolants) from an Boogie AST
 * which contains only unstructured Code (i.e., no while (and others??)
 * statements).
 * Therefore this Plugin should be used after the BoogiePreprocessor, which
 * transforms structured Boogie Code to unstructured Boogie Code.
 * 
 * This Plugin is a modified copy of Evrens CFGBuilder.
 * @author heizmann@informatik.uni-freiburg.de
 */

//TODO How to give every location the right line number
public class RecursiveCFGBuilder {
	
	/**
	 * Logger for this plugin.
	 */
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
     * Root Node of this Stalin model. I use this to store information that
     * should be passed to the next plugin. The Successors of this node are
     * exactly the initial nodes of procedures.
	 */
	private RootNode m_Graphroot;
	
	/**
	 * Maps a procedure name to the initial node of that procedure.
	 */
	private Map<String,LocNode> m_initialNode = 
								new HashMap<String,LocNode>();
	
	/**
	 * Maps a procedure name to the final node of that procedure.
	 * The final node of a procedure represents the location that is reached
	 * after executing the last statement of the procedure or after executing
	 * a return statement. At this node the ensures part of the specification is
	 * asserted (has to be checked to prove correctness of the procedure).
	 * A sequence of edges that assumes the ensures part of the specification
	 * leads to the exit node of the procedure.
	 * 
	 */
	private Map<String,LocNode> m_finalNode = 
								new HashMap<String,LocNode>();

	/**
	 * Maps a procedure name to the the exit node of that procedure.
	 * The exit node of a procedure represents an auxiliary location that is
	 * reached after assuming the ensures part of the specification. This
	 * locNode is the source of ReturnEdges which lead to the callers of this
	 * procecure.
	 */
	private Map<String,LocNode> m_exitNode = 
								new HashMap<String,LocNode>();
	
	
	/**
	 * Maps the pair of procedure name location name to the LocNode that
	 * represents this location.
	 */
	private Map<String,Map<String,LocNode>> m_LocNodes =
								new HashMap<String,Map<String,LocNode>>();
	
	/**
	 * Maps a procedure name to the requires clauses of the procedure
	 */
	private Map<String,List<Expression>> m_Requires = 
								new HashMap<String,List<Expression>>();

	/**
	 * Maps a procedure name to the requires clauses of the procedure which are
	 * not free. (A requires clause is not free if we have to proof that it
	 * holds.)
	 */
	private Map<String,List<Expression>> m_RequiresNonFree = 
								new HashMap<String,List<Expression>>();

	/**
	 * Maps a procedure name to the ensures clauses of the procedure
	 */
	private Map<String,List<Expression>> m_Ensures = 
								new HashMap<String,List<Expression>>();
	
	/**
	 * Maps a procedure name to the ensures clauses of the procedure which are
	 * not free. (A ensures clause is not free if we have to proof that it 
	 * holds.)
	 */
	private Map<String,List<Expression>> m_EnsuresNonFree = 
								new HashMap<String,List<Expression>>();
	
	/**
	 * Set of global variables defined in this program. The set of variables is
	 * represented as a map where the identifier of the variable is mapped to
	 * the type of the
	 * variable.  
	 */
	private Map<String,ASTType> m_GlobalVars = 
								new HashMap<String, ASTType>();

	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure. The set of variables is represented as a map
	 * where the identifier of the variable is mapped to the type of the
	 * variable. 
	 */
	private Map<String,Map<String,ASTType>> m_ModifiedVars = 
								new HashMap<String,Map<String,ASTType>>();
	
	
	/**
	 * Maps a pair consisting of a procedure name and an inParam identifier to
	 * the global variable that is used for passing this parameter at a
	 * procedure call in the Recursive Trace Abstraction model.
	 * A global variable is represented as a map, where the identifier of the
	 * variable is mapped to the type of the variable.
	 */
	private Map<String,Map<String,Map<String,ASTType>>> m_GlobInParams = 
						new HashMap<String,Map<String,Map<String,ASTType>>>();

	/**
	 * Maps a pair consisting of a procedure name and an outParam identifier to
	 * the global variable that is used for passing the result of a
	 * procedure call in the Recursive Trace Abstraction model.
	 * A global variable is represented as a map, where the identifier of the
	 * variable is mapped to the type of the variable.
	 */
	private Map<String,Map<String,Map<String,ASTType>>> m_GlobOutParams = 
						new HashMap<String,Map<String,Map<String,ASTType>>>();

		
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * specification of the procedure. 
	 */
	private Map<String,Procedure> m_Procedure = 
								new HashMap<String,Procedure>();
	
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * implementation of the procedure. 
	 */	
	private Map<String,Procedure> m_Implementation = 
								new HashMap<String,Procedure>();
	
	
	/**
	 * If true an InternalTransition represents a whole block, otherwise there
	 * is an InternalTransition for every single Statement.
	 */
	private boolean m_MultipleStatementsPerTransition;
	
	
   public RecursiveCFGBuilder(boolean multipleStatementsPerTransition) {
	   m_MultipleStatementsPerTransition = multipleStatementsPerTransition;
	}

   /**
	 * Build a recursive control flow graph for an unstructured boogie program.
	 * @param Unit that encodes a program.
	 * @return RootNode of a recursive control flow graph.
	 */
	public RootNode getRootNode(Unit unit) {
		// This procedure is a modified copy of Evrens CFG Builder.
		List<Declaration> declarations = new ArrayList<Declaration>();
		List<Axiom> axioms = new ArrayList<Axiom>();
		for (Declaration d : unit.getDeclarations()){
			if (d instanceof TypeDeclaration
					|| d instanceof FunctionDeclaration
					|| d instanceof ConstDeclaration
					|| d instanceof VariableDeclaration) {
				declarations.add(d);
				if (d instanceof VariableDeclaration) {
					VariableDeclaration varDecl = (VariableDeclaration) d;
					VarList[] varLists = varDecl.getVariables();
					for (VarList varList : varLists) {
						for (String identifier : varList.getIdentifiers()) {
							m_GlobalVars.put(identifier,varList.getType());
						}
					}
				}
			}
			else if (d instanceof Axiom){
				axioms.add((Axiom) d);
			}
			else if (d instanceof Procedure){
				Procedure proc = (Procedure) d;
				if (proc.getSpecification() != null && proc.getBody() != null) {
					s_Logger.warn("Specification and implementation of " +
							"procedure" + proc.getIdentifier() + " given in " +
							"one single declaration");
				}
						
				if (proc.getSpecification() != null) {
					s_Logger.info("Found specification of procedure "
							+proc.getIdentifier());
					if (m_Procedure.containsKey(proc.getIdentifier())){
						throw new UnsupportedOperationException(
								"Procedure" + proc.getIdentifier() +
								"declarated twice");
					}
					else {
						m_Procedure.put(proc.getIdentifier(), proc);
						extractContract(proc.getIdentifier());
						extractGlobParams(proc.getIdentifier());
					}
				}
				if (proc.getBody() != null) {
					s_Logger.info("Found implementation of procedure "
							+proc.getIdentifier());
					if (m_Implementation.containsKey(proc.getIdentifier())){
						throw new UnsupportedOperationException( "File " +
								"contains two implementations of procedure"
								+ proc.getIdentifier());
					}
					else {
						m_Implementation.put(proc.getIdentifier(), proc);
					}
				}
				declarations.add(proc);
			}
			else {
				throw new UnsupportedOperationException(
						"Unsupported type of Declaration");
			}
		}
		
		//Initialize the root node.
		m_Graphroot = new RootNode(declarations,
								   axioms,
								   m_Procedure,
								   m_Implementation,
								   m_LocNodes,
								   m_initialNode,
								   m_ModifiedVars,
								   m_GlobalVars,
								   m_MultipleStatementsPerTransition);
			
		// Build initial, final and exit node for all implemented procedures
		for (String procName : m_Implementation.keySet()) {
			LocNode initNode =
				new LocNode(procName + "INIT",procName,false,null,null);
			m_initialNode.put(procName, initNode);
			LocNode finalNode = 
				new LocNode(procName + "FINAL",procName,false, null, null);
			m_finalNode.put(procName, finalNode);
			LocNode exitNode =
				new LocNode(procName + "EXIT",procName,false,null,null);
			m_exitNode.put(procName, exitNode);


			new RootEdge(m_Graphroot,m_initialNode.get(procName));
		}
		
		
		// Build a control flow graph for each implementation
		ProcedureCfgBuilder procCfgBuilder = new ProcedureCfgBuilder();
		for (String procName : m_Implementation.keySet()) {
			procCfgBuilder.buildProcedureCfgFromImplementation(procName);
		}
		
		// Transform CFGs to a recursive CFG
		buildRecursiveCFG(m_Graphroot);
		
		// Add SMT annotation
		TransFormulaBuilder tfb = new TransFormulaBuilder();
		tfb.addTransitionFormulasToRCFG(m_Graphroot);
		
		return m_Graphroot;
	}
	




	/**
	 * Get the contract (requires, ensures, modified variables) of a procedure
	 * specification. Write it to m_Ensures, m_EnsuresNonFree, m_Requires, 
	 * m_RequiresNonFree and m_ModifiedVars.
	 * @param Identifier of a procedure.
	 */
	private void extractContract(String procName) {
		Procedure proc = m_Procedure.get(procName);
		Specification[] specifications = proc.getSpecification();
		
		List<Expression> ensures = new ArrayList<Expression>();
		List<Expression> ensuresNonFree = new ArrayList<Expression>();
		List<Expression> requires = new ArrayList<Expression>();
		List<Expression> requiresNonFree = new ArrayList<Expression>();
		Map<String,ASTType> modifiedVars = new HashMap<String,ASTType>();
		for (Specification spec : specifications) {
			if (spec instanceof EnsuresSpecification) {
				EnsuresSpecification ensSpec = (EnsuresSpecification) spec;
				ensures.add(ensSpec.getFormula());
				if (!ensSpec.isFree()) {
					ensuresNonFree.add(ensSpec.getFormula());
				}
			}
			else if (spec instanceof RequiresSpecification) {
				RequiresSpecification recSpec = (RequiresSpecification) spec;
				requires.add(recSpec.getFormula());
				if (!recSpec.isFree()) {
					requiresNonFree.add(recSpec.getFormula());
				}
			}
			else if (spec instanceof LoopInvariantSpecification) {
				s_Logger.warn("Found LoopInvariantSpecification" + spec + 
						"but this plugin does not use loop invariants.");
			}
			else if (spec instanceof ModifiesSpecification) {
				ModifiesSpecification modSpec = (ModifiesSpecification) spec;
				for (String ident : modSpec.getIdentifiers()) {
					if (!m_GlobalVars.containsKey(ident)) {
						throw new IllegalArgumentException("Procedure "
								+ procName + " modifies global variable "+ ident
								+ " which has not been decleared before");
					}
					modifiedVars.put(ident, m_GlobalVars.get(ident));
				}
			}
			else {
				throw new UnsupportedOperationException(
											"Unknown type of specification)");
			}
			m_Ensures.put(procName, ensures);
			m_EnsuresNonFree.put(procName, ensuresNonFree);
			m_Requires.put(procName, requires);
			m_RequiresNonFree.put(procName, requiresNonFree);
			m_ModifiedVars.put(procName, modifiedVars);
		}
	}
	
	/**
	 * Get Identifier and ASTType of inParams/outParams, construct corresponding
	 * global variables and write them to m_GlobInParams/m_GlobOutParams
	 */
	private void extractGlobParams(String procName) {
		Procedure proc = m_Procedure.get(procName);
		{
			VarList[] inParams = proc.getInParams();
			Map<String,Map<String,ASTType>> inParamGlobVars = 
					new HashMap<String,Map<String,ASTType>>();
			for (VarList varList : inParams) {
				String[] identifiers = varList.getIdentifiers();
				ASTType type = varList.getType();
				for (String identifier : identifiers) {
					String globVarName = procName + "InParam" + identifier;
					Map<String,ASTType> globVar = 
							new HashMap<String,ASTType>(1);
					globVar.put(globVarName,type);
					inParamGlobVars.put(identifier,globVar);
				}
			}
			m_GlobInParams.put(procName, inParamGlobVars);
		}
		
		{
			VarList[] outParams = proc.getOutParams();
			Map<String,Map<String,ASTType>> outParamGlobVars = 
					new HashMap<String,Map<String,ASTType>>();
			for (VarList varList : outParams) {
				String[] identifiers = varList.getIdentifiers();
				ASTType type = varList.getType();
				for (String identifier : identifiers) {
					String globVarName = procName + "OutParam" + identifier;
					Map<String,ASTType> globVar = 
							new HashMap<String,ASTType>(1);
					globVar.put(globVarName,type);
					outParamGlobVars.put(identifier,globVar);
				}
			}
			m_GlobOutParams.put(procName, outParamGlobVars);
		}
	}
	
	/**
	 * FIXME documentation
	 * @return
	 */
	private VariableDeclaration buildInOutParamVariableDeclaration() {
		
		List<VarList> inOutParamVars = new LinkedList<VarList>();
	
		for (String procName : m_GlobInParams.keySet()) {
			Map<String, Map<String, ASTType>> paramName2globVar = 
					m_GlobInParams.get(procName);
			for (String paramName : paramName2globVar.keySet()) {
				Map<String, ASTType> globVar = paramName2globVar.get(paramName);
				assert globVar.keySet().size()==1;
				for (String globVarName : globVar.keySet()) {
					ASTType globVarType = globVar.get(globVarName);
					String[] identifiers = { globVarName };
					inOutParamVars.add(new VarList(identifiers, globVarType));
				}
			}
		}
		for (String procName : m_GlobOutParams.keySet()) {
			Map<String, Map<String, ASTType>> paramName2globVar = 
					m_GlobOutParams.get(procName);
			for (String paramName : paramName2globVar.keySet()) {
				Map<String, ASTType> globVar = paramName2globVar.get(paramName);
				assert globVar.keySet().size()==1;
				for (String globVarName : globVar.keySet()) {
					ASTType globVarType = globVar.get(globVarName);
					String[] identifiers = { globVarName };
					inOutParamVars.add(new VarList(identifiers, globVarType));
				}
			}
		}
		
		return new VariableDeclaration(null, 0, null, 
										inOutParamVars.toArray(new VarList[0]));
	}
	

	
	private Expression getConjunction(List<Expression> expressions) {
		if (expressions == null || expressions.isEmpty()) {
			return null;
		}
		else {
			Expression conj = expressions.remove(0);
			for (Expression expr : expressions) {
				conj = new BinaryExpression(PrimitiveType.boolType,
											BinaryExpression.Operator.LOGICAND,
											conj,
											expr);
			}
			return conj;
		}	
	}
	
	
	
	private Expression getNegation(Expression expr) {
		if (expr == null) {
			return null;
		}
		else {
			return new UnaryExpression(PrimitiveType.boolType,
									   UnaryExpression.Operator.LOGICNEG,
									   expr);
		}
	}
	

	
	/**
	 * Transform a set of CFGs to a recursive CFG. Search for SummaryEdges that
	 * summarize calls of implemented procedures. Add CallEdge from the summary
	 * edge source to the initial location of the called procedure. Add
	 * ReturnEdge from the called procedures exit node to the summary edges
	 * target.
	 * @param RootNode whose successors are the initial nodes of CFGs.
	 */
	public void buildRecursiveCFG(RootNode root) {
		//Traverse the CFG and search for SummaryEdges
		Collection<SummaryEdge> summaryEdges = new LinkedList<SummaryEdge>();
		List<LocNode> queue = new LinkedList<LocNode>();
		Set<LocNode> visited = new HashSet<LocNode>();
		for (INode succNode : root.getOutgoingNodes()) {
			queue.add((LocNode)succNode);
			visited.add((LocNode)succNode);
		}
		while (!queue.isEmpty()) {
			LocNode locNode = queue.remove(0);
			for (IEdge edge : locNode.getOutgoingEdges()) {
				if (edge instanceof SummaryEdge) {
					SummaryEdge summary = (SummaryEdge) edge;
					String procName= summary.getCallStatement().getMethodName();
					if (m_Implementation.containsKey(procName))
					summaryEdges.add((SummaryEdge) edge);
				}
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
		//Add corresponding CallEdges and ReturnEdges
		for (SummaryEdge edge : summaryEdges) {
			addCallTransitionAndReturnTransition(edge);
		}
	}
	
	
	/**
	 * Add CallEdge from SummaryEdge source to the initial location of the
	 * called procedure. Add ReturnEdge from the called procedures exit node to
	 * the summary edges target.
	 * @param SummaryEdge that summarizes execution of an implemented procedure.
	 */
	private void addCallTransitionAndReturnTransition(SummaryEdge summary) {
		CallStatement st = summary.getCallStatement();
		String callee = st.getMethodName();
		assert(m_initialNode.containsKey(callee)) : "Source code contains" +
		" call of " + callee+ " but no such procedure.";

		
		// Add call transition from callerNode to procedures initial node
		LocNode callerNode = (LocNode) summary.getSource();
		LocNode calleeInitLoc = m_initialNode.get(callee);
		CallEdge callEdge = new CallEdge(callerNode,calleeInitLoc,
				     st,m_Procedure.get(callee),m_ModifiedVars.get(callee));
		
		LocNode returnNode = (LocNode) summary.getTarget();
		LocNode calleeExitLoc = m_exitNode.get(callee);
		new ReturnEdge(calleeExitLoc,returnNode, st,
			callEdge.getCallAnnotations(),m_Procedure.get(callee),callerNode);
	}
	
	
	
//	private AssignmentStatement parameterPassing(CallStatement st) {
//		Procedure proc = m_Procedure.get(st.getMethodName());
//		VarList[] inParams = proc.getInParams();
//		VarList[] outParams = proc.getOutParams();
//		String[] lhs = st.getLhs();
//		Expression[] arguments = st.getArguments();
//		
//		VariableLHS[] globalInParams = new VariableLHS[inParams.length];
//		
//		
//		
////		Expression[] arguments = st.getArguments();
//		List<VariableLHS> parameterList = new LinkedList<VariableLHS>();
//		VarList[] inParams = proc.getInParams();
//		for (VarList varList : inParams) {
//			String[] identifiers = varList.getIdentifiers();
//			IType type = varList.getType().getBoogieType();
//			for (String identifier : identifiers) {
//				parameterList.add(new VariableLHS(type, identifier));
//			}
//		}
//		s_Logger.debug("Call "+st+" has "+arguments.length+" arguments");
//		s_Logger.debug("Procedure"+st.getMethodName()+" has "
//				+parameterList.size()+"(in)parameters");
//		if (arguments.length!=parameterList.size()) {
//			throw new IllegalArgumentException("CallStatement" + st + 
//					"has wrong number of arguments");
//		}
//		VariableLHS[] lhs = parameterList.toArray(new VariableLHS[0]);
//		new AssignmentStatement(null,0, lhs,arguments);
//		return null;
//		
//	}
	
	
	
	
	/**
	 * Build control flow graph of single procedures. 
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private class ProcedureCfgBuilder {

		/**
		 * Maps a Label identifier to the LocNode that represents this Label in
		 * the CFG.
		 */
		private Map<String,LocNode> m_procLocNodes = 
										new HashMap<String,LocNode> ();
		
		/**
		 * Name of that last Label for which we constructed a LocNode 
		 */
		String m_lastLabelName;
		
		/**
		 * Distance to the last LocNode that was constructed as
		 * representative of a label. 
		 */
		int m_locSuffix;
		
		/**
		 * Element at which we continue building the CFG.
		 * This should be a 
		 * - LocNode if the last processed Statement was a Label or 
		 * 			a CallStatement
		 * - TransEdge if the last processed Statement was Assume,
		 *        Assignment, Havoc or Assert.
		 * - null if the last processed Statement was Goto or Return.
 		 */
		IElement m_current;
		
		/**
		 * List of auxiliary edges, which represent Gotos and get removed later.
		 */
		List<GotoEdge> m_GotoEdges = new LinkedList<GotoEdge>();
		
		/**
		 * Name of the procedure for which the CFG is build (at the moment) 
		 */
		String m_currentProcedureName;
				
		/**
		 * Builds the control flow graph of a single procedure according to a
		 * given implementation. 
		 * @param Identifier of the procedure for which the CFG will be build.
		 */
		private void buildProcedureCfgFromImplementation(String procName)
		{
			m_currentProcedureName = procName;
			
			Statement[] statements = 
							m_Implementation.get(procName).getBody().getBlock();
			if (statements.length==0) {
				throw new UnsupportedOperationException(
											 "Procedure contains no statement");
			}
			
			//initialize the Map from labels to LocNodes for this procedure
			m_procLocNodes = new HashMap<String,LocNode>();
			m_LocNodes.put(procName, m_procLocNodes);

			//The last processed Statement. This is only used in assertions to
			//make debugging easier.
			Statement lastSt;
				
			s_Logger.debug("Start construction of the CFG for" + procName);
			
			{
				//first LocNode is the initial node of the procedure
				LocNode locNode = m_initialNode.get(procName);
				m_lastLabelName = locNode.getLocationName();
				m_locSuffix = 0;
				m_procLocNodes.put(m_lastLabelName, locNode);
				m_current = locNode;

				//create an auxiliary label as last Statement (this is only used
				//for debugging)
				lastSt = new Label(null,0,null);

				//Assume everything mentioned in the requires specification
				List<Expression> requires = m_Requires.get(procName);
				if (requires != null && !requires.isEmpty()) {
					AssumeStatement st;
					for (Expression expr : requires) {
						st = new AssumeStatement(null,0,expr);
						processAssuAssiHavoStatement(st,Origin.REQUIRES);
						lastSt = st;
					}
				}
			}
			
			for (Statement st : statements) {
				
				if (st instanceof Label) {
					if (m_current instanceof LocNode) {
						assert (lastSt instanceof Label) : "If st is Label" +
								" and m_current is LocNode lastSt is Label";
						s_Logger.warn("Two Labels in a row: "+m_current+
								" and "+((Label)st).getName() + "." + 
								" I am expecting that at least one was" +
								" introduced by the user (or vcc). In the" +
								" CFG only the first label of those two (or" +
								" more) will be used");
					}
					if (m_current instanceof TransEdge) {
						assert (lastSt instanceof AssumeStatement
								|| lastSt instanceof AssignmentStatement 
								|| lastSt instanceof HavocStatement
								|| lastSt instanceof AssertStatement
								|| lastSt instanceof CallStatement) : "If st" +
								" is a Label and the last constructed node" +
								" was a TransEdge, then the last" +
								" Statement must not be a Label, Return or" +
								" Goto";
						s_Logger.warn("Label in the middle of a codeblock.");
					}
		
					processLabel((Label)st);
				}
					
				else if (st instanceof AssumeStatement 
						|| st instanceof AssignmentStatement 
						|| st instanceof HavocStatement)
				{
					if (m_current instanceof TransEdge) {
						assert (lastSt instanceof AssumeStatement
								|| lastSt instanceof AssignmentStatement 
								|| lastSt instanceof HavocStatement
								|| lastSt instanceof AssertStatement
								|| lastSt instanceof CallStatement) : "If the" +
								" last constructed node is a TransEdge, then" +
								" the last Statement must not be a Label," +
								" Return or Goto. (i.e. this is not the first" +
								" Statemnt of the block)";
					}
					processAssuAssiHavoStatement(st,Origin.IMPLEMENTATION);
				}
				
				else if (st instanceof AssertStatement)
				{
					if (m_current instanceof TransEdge) {
						assert (lastSt instanceof AssumeStatement
								|| lastSt instanceof AssignmentStatement 
								|| lastSt instanceof HavocStatement
								|| lastSt instanceof AssertStatement
								|| lastSt instanceof CallStatement) : "If the" +
								" last constructed node is a TransEdge, then" +
								" the last Statement must not be a Label," +
								" Return or Goto. (i.e. this is not the first" +
								" Statement of the block)";
					}
					processAssertStatement((AssertStatement) st);
				}
				
				else if (st instanceof GotoStatement) {
					assert (! (lastSt instanceof GotoStatement)) : 
						"Two Gotos in a row";
					processGotoStatement( (GotoStatement) st);
				}
				
				else if (st instanceof CallStatement) {
					if (m_current instanceof TransEdge) {
						assert (lastSt instanceof AssumeStatement
								|| lastSt instanceof AssignmentStatement 
								|| lastSt instanceof HavocStatement
								|| lastSt instanceof AssertStatement
								|| lastSt instanceof CallStatement) : 
									"If m_current is a TransEdge, then lastSt" +
									" must not be a Label, Return or Goto." +
									" (i.e. this is not the first Statemnt" +
									" of the block)";
					}
					if (m_current instanceof LocNode) {
						assert (lastSt instanceof Label
								|| lastSt instanceof CallStatement) :
									"If m_current is LocNode, then st is" +
									" first statement of a block or fist" +
									" statement after a call";
					}
					processCallStatement((CallStatement) st);
				}
					
				else if (st instanceof ReturnStatement) {
					processReturnStatement();
				}

				else {
					throw new UnsupportedOperationException("At the moment" +
							" only Labels, Assert, Assume, Assignment, Havoc" +
							" and Goto statements are supported");
				}
				lastSt = st;
			}
			
			// If there is no ReturnStatement at the end of the procedure act
			// like there would have been one.
			if (!(lastSt instanceof ReturnStatement)) {
				processReturnStatement();
			}
			
			// Assume the ensures specification at the end of the procedure.
			List<Expression> ensures = m_Ensures.get(m_currentProcedureName);
			if (ensures == null || ensures.isEmpty()) {
				ensures = new ArrayList<Expression>(1);
				ensures.add(new BooleanLiteral(BoogieType.boolType, true));
			}
			LocNode finalNode = m_finalNode.get(m_currentProcedureName); 
			m_lastLabelName = finalNode.getLocationName();
			m_procLocNodes.put(m_lastLabelName, finalNode);
			m_locSuffix = 0;
			m_current = finalNode;
			
			for (Expression expr : ensures) {
				AssumeStatement st = 
						new AssumeStatement(procName, m_locSuffix, expr);
				processAssuAssiHavoStatement(st,Origin.ENSURES);
			}
			LocNode exitNode = m_exitNode.get(m_currentProcedureName);
			m_lastLabelName = exitNode.getLocationName();
			m_procLocNodes.put(m_lastLabelName, exitNode);
			((TransEdge) m_current).connectTarget(exitNode);
			
			
			// Violations against the ensures part of the procedure 
			// specification
			List<Expression> ensuresNonFree = 
					m_EnsuresNonFree.get(m_currentProcedureName);
			if (ensuresNonFree != null && !ensuresNonFree.isEmpty()) {
				String errorLocName = m_currentProcedureName + 
															"EnsuresViolation";
				LocNode errorLocNode = new LocNode(errorLocName,
												m_currentProcedureName,
												true,
												null,
												null);
				m_procLocNodes.put(errorLocName, errorLocNode);
				for (Expression expr : ensuresNonFree) {
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(null,0,getNegation(expr));
					new InternalEdge(finalNode, errorLocNode, assumeSt, 
															Origin.ENSURES);
				}
			}
			
						
			//Remove auxiliary GotoTransitions
			s_Logger.debug("Starting removal of auxiliaryGotoTransitions");
			while (!(m_GotoEdges.isEmpty())) {
				GotoEdge gotoEdge = m_GotoEdges.remove(0);
				removeAuxiliaryGoto(gotoEdge);
			}
			
		}
		
		
		/**
		 * Remove GotoEdge from a CFG in a way that the program behaviour is not
		 * changed. 
		 */
		private void removeAuxiliaryGoto(GotoEdge gotoEdge) {
			LocNode mother = (LocNode) gotoEdge.getSource();
			LocNode child = (LocNode) gotoEdge.getTarget();
			
			// Target of a goto should never be an error location.
			// If this assertion will fail some day. A fix might be that
			// mother has to become an error location.
			assert(!child.getProgramPoint().isErrorLocation());
			
			for (IEdge grandchild : child.getOutgoingEdges()) {
				if (grandchild instanceof CallEdge) {
					s_Logger.info("Will not remove gotoEdge" + gotoEdge 
							+ "since this would involve adding/removing call" +
							"and return edges and bring my naive goto" +
							" replacing algorithm into terrible trouble");
					return;
				}
			}
			
			mother.removeOutgoingEdge(gotoEdge);
			gotoEdge.setSource(null);
			gotoEdge.setTarget(null);
			child.removeIncomingEdge(gotoEdge);
			s_Logger.debug("Removed GotoEdge from" + mother	+ " to "+ child);
			if (mother==child){
				s_Logger.debug("GotoEdge was selfloop");
			}
			else {
				if (child.getIncomingEdges().isEmpty() ||
										mother.getOutgoingEdges().isEmpty()) {
					s_Logger.debug(mother + " has no sucessors any more or " +
							child + "has no predecessors any more.");
					s_Logger.debug(child + " gets absorbed by " + mother);
					mergeLocNodes(child, mother);
				}
				else {
					//Not allowed to merge mother and child in this case
					s_Logger.debug(child + " has " + 
							child.getIncomingEdges().size() + " predecessors," +
									" namely " + child.getIncomingNodes());
					s_Logger.debug(mother + " has " + 
							mother.getIncomingEdges().size() + " successors" +
									", namely " + mother.getOutgoingNodes());
					s_Logger.debug("Adding for every successor" +
							" transition of " + child + " a copy of that" +
							" transition as successor of "+mother);
					for (IEdge grandchild : child.getOutgoingEdges()) {
						
						TransEdge edge = copyTransEdgeWithSuccessors(
														(TransEdge) grandchild);
						if (edge instanceof GotoEdge) {
							m_GotoEdges.add((GotoEdge)edge);
						}
						mother.addOutgoingEdge(edge);
						edge.setSource(mother);
					}
				}
			}
		}
		
		

		
		/**
		 * Builds the control flow graph of a single procedure according to a
		 * given specification. Use this if no implementation is available.
		 * @param Name of the procedure for which the CFG will be build.
		 */
		private void buildProcedureCfgWithoutImplementation(String procName)
		{
			m_currentProcedureName = procName;
			
			s_Logger.debug("Start construction of the CFG for" + procName);
			
			//first LocNode is the initial node of the procedure
			LocNode initNode = m_initialNode.get(procName);
			m_lastLabelName = initNode.getLocationName();
			m_locSuffix = 0;
			m_procLocNodes.put(m_lastLabelName, initNode);
			m_current = initNode;


			//get the final Node
			LocNode finalNode = m_finalNode.get(procName);			
			
			
			//Assume everything mentioned in the requires specification
			List<Expression> requires = m_Requires.get(procName);
			if (requires == null || requires.isEmpty()) {
				requires = new ArrayList<Expression>(1);
				requires.add(new BooleanLiteral(BoogieType.boolType, true));
			}
			for (Expression expr : requires) {
				AssumeStatement st = 
							new AssumeStatement(procName, m_locSuffix, expr);
				processAssuAssiHavoStatement(st,Origin.REQUIRES);
			}
			((InternalEdge) m_current).connectTarget(finalNode);
			

			//Assume every expression of the ensures specification
			List<Expression> ensures = m_Ensures.get(m_currentProcedureName);
			if (ensures == null || ensures.isEmpty()) {
				ensures = new ArrayList<Expression>(1);
				ensures.add(new BooleanLiteral(BoogieType.boolType, true));
			}
			m_lastLabelName = finalNode.getLocationName();
			m_locSuffix = 0;
			m_current = finalNode;
			for (Expression expr : ensures) {
				AssumeStatement st = 
							new AssumeStatement(procName, m_locSuffix, expr);
				processAssuAssiHavoStatement(st,Origin.ENSURES);
			}
			LocNode exitNode = m_exitNode.get(procName);
			((TransEdge) m_current).connectTarget(exitNode);
		}
		
		
		
		
		
		/** 
		 * Get the LocNode that represents a label.
		 * If there is already a LocNode that represents this Label return
		 * this representative. Otherwise construct a new LocNode that
		 * becomes the representative for this label.
		 * 	
		 * @param labelName
		 * 			Name of the Label for which you want the corresponding
		 * 			 LocNode.
		 * @param st
		 * 			Statement whose (STALIN) Location should be added to this
		 * 			LocNode. If this method is called while processing a
		 *  		GotoStatement the Statement can be set to null, since the
		 *  		Location will be overwritten, when this method is called
		 *  		with the correct Label as second parameter.
		 * @return
		 * 			LocNode that is the representative for labelName. 
		 */
		@SuppressWarnings("deprecation")
		private LocNode getLocNodeforLabel(String labelName, Statement st) {
			if (m_procLocNodes.containsKey(labelName)) {
				LocNode locNode = m_procLocNodes.get(labelName); 
				s_Logger.debug("LocNode for "+labelName+" already" +
						" constructed, namely: "+locNode);
				if (st instanceof Label 
						&& locNode.getLocationName() == labelName) {
					Location loc = 
						new Location(st.getFilename(),"",st.getLineNr());
					locNode.getPayload().setLocation(loc);
				}
				return locNode; 
			}
			else {
				LocNode locNode = 
					new LocNode(labelName,m_currentProcedureName,false,st,null);
				m_procLocNodes.put(labelName, locNode);
				s_Logger.debug("LocNode for "+labelName+" has not" +
						" existed yet. Constructed it");
				return locNode;
			}
		}
		


		private void processLabel(Label st) {
			String labelName = ((Label) st).getName();
			if (m_current instanceof LocNode) {
				//from now on this label is represented by m_current
				LocNode oldNodeForLabel = m_procLocNodes.get(labelName);
				if (oldNodeForLabel != null) {
					mergeLocNodes(oldNodeForLabel, (LocNode) m_current);
				}
				m_procLocNodes.put(labelName,(LocNode) m_current);	
			}
			else // (m_current instanceof TransEdge) or m_current = null 
			{
				m_lastLabelName = labelName;
				m_locSuffix = 0;

				//is there already a LocNode that represents this
				//label? (This can be the case if this label was destination
				//of a goto statement) If not construct the LocNode.
				//If yes, add the Location Object to the existing LocNode.
				LocNode locNode = getLocNodeforLabel(labelName,st);
				
				if (m_current instanceof TransEdge) {
					((IEdge) m_current).setTarget(locNode);
					locNode.addIncomingEdge((TransEdge) m_current);
				}			
				m_current = locNode;
			}
		}
		
		private void processAssuAssiHavoStatement(Statement st, Origin origin) {
			if (m_current instanceof LocNode) {
				m_current = 
					new InternalEdge((LocNode) m_current, null, st, origin);
			}
			else if (m_current instanceof InternalEdge) {
				if (m_MultipleStatementsPerTransition) {
					((InternalEdge)m_current).addStatement(st);
				}
				else {
					String locName = m_lastLabelName+"."+(++m_locSuffix);
					LocNode locNode = new LocNode(locName,
										 		  m_currentProcedureName,
										 		  false,
										 		  st,
										 		  (TransEdge)m_current);
					m_procLocNodes.put(locName, locNode);
					m_current = new InternalEdge(locNode, null, st, origin);
				}
			}
			else {
				//m_current must either be LocNode or TransEdge 
				throw new IllegalArgumentException();
			}
		}

		private void processAssertStatement(AssertStatement st) {
			if (m_current instanceof InternalEdge) {
				String locName = m_lastLabelName+"."+(++m_locSuffix);
				LocNode locNode = new LocNode(locName,
									 		  m_currentProcedureName,
									 		  false,
									 		  st,
									 		  (TransEdge)m_current);
				m_procLocNodes.put(locName, locNode);
				m_current = locNode;
			}
			LocNode locNode = (LocNode) m_current;
			Expression assertion = ((AssertStatement) st).getFormula();
			AssumeStatement assumeError = new AssumeStatement(
					st.getFilename(), st.getLineNr(), getNegation(assertion));
			String errorLocName = locNode.getLocationName() + "Violation";
			LocNode errorLocNode = new LocNode(errorLocName,
			 		  m_currentProcedureName,
			 		  true,
			 		  st,
			 		  null);
			m_procLocNodes.put(errorLocName, errorLocNode);
			new InternalEdge(locNode,errorLocNode,assumeError,Origin.ASSERT);
			AssumeStatement assumeSafe = new AssumeStatement(
					st.getFilename(),st.getLineNr(),assertion);
			//add a new TransEdge labeled with st as successor of the
			//last constructed LocNode
			m_current = new InternalEdge(locNode,null,assumeSafe,Origin.ASSERT);
		}
			
		
		private void processGotoStatement(GotoStatement st) {
			String[] targets = ((GotoStatement) st).getLabels();
			assert (targets.length!=0) : "Goto must have at least one target";
			s_Logger.debug("Goto statement with "+targets.length+" targets.");	
			LocNode locNode;
			if (m_current instanceof TransEdge) {
				String locName = m_lastLabelName+"."+(++m_locSuffix);
				locNode = new LocNode(locName,
	                    			  m_currentProcedureName,
	                    			  false,
									  st,
									  (TransEdge)m_current);
				m_procLocNodes.put(locName, locNode);
			}
			else if (m_current instanceof LocNode) {
				locNode = (LocNode)m_current;
			}
			else {
				//m_current must either LocNode or TransEdge 
				throw new IllegalArgumentException();
			}
			for (String label: targets) {
				//Add an auxiliary GotoEdge and a LocNode
				//for each target of the GotoStatement.
				LocNode targetLocNode = getLocNodeforLabel(label, null);
				m_GotoEdges.add(new GotoEdge(locNode, targetLocNode));
			}
			//We have not constructed a new node that should be used in the
			//next iteration step, therefore setting m_current to null.
			m_current = null;
		}
		
		private void processCallStatement(CallStatement st) {
			LocNode locNode;
			if (m_current instanceof TransEdge) {
				String locName = m_lastLabelName+"."+(++m_locSuffix);
				locNode = new LocNode(locName,
	 				   				  m_currentProcedureName,
	 				   				  false,
	 				   				  st,
						   			  (TransEdge)m_current);
				m_procLocNodes.put(locName, locNode);
			}
			else if (m_current instanceof LocNode) {
				locNode = (LocNode)m_current;
			}
			else {
				//m_current must be either LocNode or TransEdge 
				throw new IllegalArgumentException();
			}
			String locName = m_lastLabelName+"."+(++m_locSuffix);
			LocNode returnNode = new LocNode(locName,
	                 						 m_currentProcedureName,
	                 						 false,
	                 						 st,
	                 						 null);
			m_procLocNodes.put(locName, returnNode);
			//add summary edge 
			new SummaryEdge(locNode, returnNode, st);
			m_current = returnNode;
			
			// Violations against the requires part of the procedure 
			// specification
			List<Expression> requiresNonFree = 
					m_RequiresNonFree.get(st.getMethodName());
			if (requiresNonFree != null && !requiresNonFree.isEmpty()) {
				String errorLocName = st.getMethodName() + "RequiresViolation";
				LocNode errorLocNode = new LocNode(errorLocName,
												m_currentProcedureName,
												true,
												st,
												null);
				m_procLocNodes.put(errorLocName, errorLocNode);
				for (Expression expr : requiresNonFree) {
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(null,0,getNegation(expr));
					new InternalEdge(locNode, errorLocNode, assumeSt, 
															Origin.REQUIRES);
				}
			}
		}
		
		//FIXME problem if last statement is goto
		private void processReturnStatement() {
			//If m_current is a transition add as successor the final Node
			//of this procedure.
			//If m_current is a location replace it with the final Node of
			//this procedure.
			LocNode finalNode = m_finalNode.get(m_currentProcedureName);
			if (m_current instanceof TransEdge) {
				TransEdge transEdge = (TransEdge)m_current;
			transEdge.connectTarget(finalNode);
			s_Logger.debug("Constructed TransEdge "+transEdge+
					"as predecessr of "+m_finalNode);
			}
			else if (m_current instanceof LocNode) {
				mergeLocNodes((LocNode)m_current,finalNode);
				s_Logger.debug("Replacing "+m_current+" by "+finalNode);
			}
			else {
				//m_current must be either LocNode or TransEdge 
				throw new IllegalArgumentException();
			}
			//No new nodes created, set m_current to null
			m_current = null;
		}
		
	
		
		/**
		 * Merge one LocNode into another. The oldLocNode will be merged into
		 * the newLocNode. The newLocNode gets connected to all
		 * incoming/outgoing transitions of the oldLocNode. The oldLocNode
		 * looses connections to all incoming/outgoing transitions. If the
		 * oldLocNode was representative for a Label the new location will from
		 * now on be the representative of this Label.
		 * @param oldLocNode
		 * 			LocNode that gets merged into the newLocNode. Must not 
		 * 			represent an error location.		  			
		 * @param newLocNode
		 * 			LocNode that absorbes the oldLocNode.
		 */
		private void mergeLocNodes(LocNode oldLocNode,
				                         LocNode newLocNode) {
			//oldLocNode must not represent an error location
			assert (!oldLocNode.getProgramPoint().isErrorLocation());
			if (oldLocNode == newLocNode) {
				return;
			}

			for (IEdge transEdge : oldLocNode.getIncomingEdges()) {
				newLocNode.addIncomingEdge(transEdge);
				transEdge.setTarget(newLocNode);
			}
			oldLocNode.removeAllIncoming();
			for (IEdge transEdge : oldLocNode.getOutgoingEdges()) {
				newLocNode.addOutgoingEdge(transEdge);
				transEdge.setSource(newLocNode);
			}
			oldLocNode.removeAllOutgoing();

			//If the LocNode that should be replaced was constructed for a
			//label it is in m_locNodeOf and the representative for this label
			//should be updated accordingly. 
			if (m_procLocNodes.containsKey(oldLocNode.getLocationName())) {
				m_procLocNodes.put(oldLocNode.getLocationName(),
						newLocNode);
			}
		}
		

		
		/**
		 * Make a copy of a TransEdge without incoming edges. The copy is
		 * connected to all successors of the Original, but has no predecessors.
		 * The 'Content' of the TransEdge is not copied (uses just
		 * references to the same 'Contents'). This method is only used for
		 * removing GotoEdges.
		 * @param edge
		 * 		TransEdge that should be copied.
		 * @return
		 * 		A TransEdge of the same Type as the input.
		 */
		private TransEdge copyTransEdgeWithSuccessors(TransEdge edge){
			TransEdge newEdge;
			LocNode target = (LocNode) edge.getTarget();
			if (edge instanceof InternalEdge) {
				newEdge = new InternalEdge(null,target,edge.getPayload());
			}
			else if (edge instanceof CallEdge) {
				newEdge = new CallEdge(null,target,edge.getPayload());
			}
			else if (edge instanceof ReturnEdge) {
				LocNode caller = ((ReturnEdge)edge).getCallerNode();
				newEdge = new ReturnEdge(null,target,edge.getPayload(), caller);
			}
			else if (edge instanceof GotoEdge) {
				newEdge = new GotoEdge(null,target);
			}
			else if (edge instanceof SummaryEdge) {
				newEdge = new SummaryEdge(null,target,edge.getPayload());
			}
			else {
				throw new IllegalArgumentException("Input must be either an" +
						" InternalEdge, CallEdge, ReturnEdge, GotoEdge or" +
						" SummaryEdge");
			}
			return newEdge;
		}
	}
}
