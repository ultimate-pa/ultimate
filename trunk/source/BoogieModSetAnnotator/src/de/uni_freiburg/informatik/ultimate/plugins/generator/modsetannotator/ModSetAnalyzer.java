/*
 * Copyright (C) 2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieModSetAnnotator plug-in.
 * 
 * The ULTIMATE BoogieModSetAnnotator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieModSetAnnotator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieModSetAnnotator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieModSetAnnotator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieModSetAnnotator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.modsetannotator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.ModelType;

/**
 * This class is an AST-Visitor that extends the Boogie Type Checker, it
 * computes the modifies sets of all procedures
 */
public class ModSetAnalyzer extends BoogieTransformer implements IUnmanagedObserver {

	private Map<String, Set<String>> m_ModifiedGlobals;
	private Set<String> m_Globals;
	private IUltimateServiceProvider m_Services;
	private ILogger logger;
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
				Set<String> modifiedGlobals = m_ModifiedGlobals.get(proc.getKey());
				assert(modifiedGlobals != null);
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
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	private void processGlobalVariableDeclaration(VariableDeclaration varDecl) {
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
				if (logger.isDebugEnabled())
					logger.debug("Processing procedure " + proc.getIdentifier());
				m_CurrentProcedure = proc.getIdentifier();
				m_ModifiedGlobals.put(m_CurrentProcedure, new HashSet<String>());
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
