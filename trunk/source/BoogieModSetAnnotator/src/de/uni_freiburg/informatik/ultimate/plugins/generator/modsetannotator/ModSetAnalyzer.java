/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.modsetannotator;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

/**
 * This class is an AST-Visitor that extends the Boogie Type Checker, it
 * computes the modifies sets of all procedures
 */
public class ModSetAnalyzer extends BoogieTransformer implements
		IUnmanagedObserver {

	private Map<String, Set<String>> m_ModifiedGlobals;
	private Set<String> m_Globals;
	private IUltimateServiceProvider m_Services;
	private Logger logger;
	private String m_CurrentProcedure;
	private Map<String, Set<String>> m_CallGraph;

	public ModSetAnalyzer(IUltimateServiceProvider services) {
		m_Services = services;
		logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	protected Map<String, Set<String>> getModifiedGlobals() {
		return m_ModifiedGlobals;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			Unit unit = (Unit) root;
			m_Globals = new HashSet<String>();
			m_ModifiedGlobals = new HashMap<String, Set<String>>();
			m_CallGraph = new HashMap<String, Set<String>>();
			// First pass: Collect all global variable declarations
			for (Declaration decl : unit.getDeclarations()) {
				if (decl instanceof VariableDeclaration)
					processGlobalVariableDeclaration((VariableDeclaration) decl);
			}

			// Second pass: Process all declarations
			for (Declaration decl : unit.getDeclarations()) {
				processDeclaration(decl);
			}

			// Propagate transitive modifies
			propagateModifies();
			return false;
		}
		return true;
	}

	private void propagateModifies() {
		for (Entry<String, Set<String>> proc : m_CallGraph.entrySet()) {
			// TODO: do this only for graph roots
			for (String callee : proc.getValue()) {
				HashSet<String> visited = new HashSet<String>();
				visited.add(proc.getKey());
				Set<String> modifiedGlobals = m_ModifiedGlobals.get(proc
						.getKey());
				assert (modifiedGlobals != null);
				modifiedGlobals.addAll(getModifiesRecursive(visited, callee));
			}
		}
	}

	private Set<String> getModifiesRecursive(Set<String> visited, String proc) {
		Set<String> result = new HashSet<String>();
		if (visited.contains(proc))
			return result;
		visited.add(proc);
		Set<String> modifiedGlobals = m_ModifiedGlobals.get(proc);
		if (modifiedGlobals != null)
			result.addAll(modifiedGlobals);
		Set<String> callees = m_CallGraph.get(proc);
		if (callees != null) {
			for (String callee : callees) {
				result.addAll(getModifiesRecursive(visited, callee));
			}
		}
		return result;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex,
			int numberOfModels) throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	private void processGlobalVariableDeclaration(VariableDeclaration varDecl) {
		DeclarationInformation declInfo = new DeclarationInformation(
				StorageClass.GLOBAL, null);
		for (VarList varlist : varDecl.getVariables()) {
			for (String id : varlist.getIdentifiers()) {
				m_Globals.add(id);
			}
		}
	}

	@Override
	protected Declaration processDeclaration(Declaration decl) {
		m_CurrentProcedure = null;
		if (decl instanceof Procedure) {
			Procedure proc = ((Procedure) decl);
			if (proc.getBody() != null) { // We are processing an implementation
				m_CurrentProcedure = proc.getIdentifier();
				m_ModifiedGlobals
						.put(m_CurrentProcedure, new HashSet<String>());
				m_CallGraph.put(m_CurrentProcedure, new HashSet<String>());
			}
		}
		return super.processDeclaration(decl);
	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		String identifier = null;
		if (m_CurrentProcedure != null && lhs instanceof VariableLHS) {
			identifier = ((VariableLHS) lhs).getIdentifier();
			if (m_Globals.contains(identifier))
				m_ModifiedGlobals.get(m_CurrentProcedure).add(identifier);
		}
		return super.processLeftHandSide(lhs);
	}

	@Override
	protected Statement processStatement(Statement statement) {
		if (m_CurrentProcedure != null && statement instanceof CallStatement) {
			CallStatement call = (CallStatement) statement;
			String method = call.getMethodName();
			// Only add if it is not a recursive call
			if (!method.equals(m_CurrentProcedure)) {
				m_CallGraph.get(m_CurrentProcedure).add(method);
			}
		}
		return super.processStatement(statement);
	}
}