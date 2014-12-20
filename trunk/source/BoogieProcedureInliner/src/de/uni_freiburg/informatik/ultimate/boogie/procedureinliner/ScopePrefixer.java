package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring.MappingExecutor;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Observer, which unites specifications and implementations of procedures
 * and gives every global variable and local variable a globally unique name.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ScopePrefixer implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private Unit mAstUnit;

	public ScopePrefixer(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() throws Throwable {
	}

	@Override
	public void finish() throws Throwable {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return true; // TODO only if something has really changed
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		// Store the first node of the AST and use it to process the AST manually
		if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			uniteProcedures();
			addScopePrefix();
			return false;
		}
		return true;
	}

	// unite procedure specifications with their implementations in mAstUnit 
	private void uniteProcedures() {
		// Filter the procedure objects from the AST
		ArrayList<Procedure> implementations = new ArrayList<Procedure>(); // procedure implementation only
		HashMap<String, Procedure> declarations = new HashMap<String, Procedure>(); // procedure declaration only
		ArrayList<Procedure> procedures = new ArrayList<Procedure>(); // both, procedure implementation and declaration
		ArrayList<Declaration> others = new ArrayList<Declaration>(); // everything other from the ast unit
		for (Declaration declaration : mAstUnit.getDeclarations()) {
			if (declaration instanceof Procedure) {
				Procedure p = (Procedure) declaration;
				if (p.getSpecification() == null) {
					implementations.add(p);
				} else if (p.getBody() == null) { 
					declarations.put(p.getIdentifier(), p);
				} else { 
					procedures.add(p);
				}
			} else {
				others.add(declaration);
			}
		}

		// Unite all implementations with their specifications
		for (Procedure implementation : implementations) {
			Procedure declaration = declarations.remove(implementation.getIdentifier());
			if (declaration == null) {
				mLogger.error("No declaration for procedure implementation \"" + implementation.getIdentifier() + "\".");
				// TODO throw exception, using mServices (see TypeChecker, Line 1156)
				throw new AssertionError();
			}
			procedures.add(unite(declaration, implementation));
			declarations.remove(implementation.getIdentifier());
		}
		others.addAll(procedures);
		others.addAll(declarations.values()); // remaining declarations without implementations
		mAstUnit.setDeclarations(others.toArray(new Declaration[others.size()]));
	}

	/**
	 * Unites separate declaration and implementation of a procedure into one procedure object.
	 * parameters can have different names in declaration and implementation.
	 * The variable names from the implementation are kept,
	 * the variables from the declaration's specification are refactored.
	 * @param declaration    Procedure declaration (without body)
	 * @param implementation Implementation of the same procedure
	 * @return United procedure
	 */
	private Procedure unite(Procedure declaration, Procedure implementation) {
		HashMap<String, String> mapping = generateMapping(declaration.getInParams(), implementation.getInParams());
		mapping.putAll(generateMapping(declaration.getOutParams(), implementation.getOutParams()));
		MappingExecutor mappingExec = new MappingExecutor(mapping);
		// TODO Also unite where clauses (is this even possible)?
		// TODO refactor, unite Attributes?
		if (declaration.getAttributes().length > 0 || implementation.getAttributes().length > 0)
			throw new UnsupportedOperationException("Attributes arn't supported yet.");
		return new Procedure(implementation.getLocation(), new Attribute[0], declaration.getIdentifier(),
				implementation.getTypeParams(), implementation.getInParams(), implementation.getOutParams(),
				mappingExec.map(declaration.getSpecification()), implementation.getBody());
	}

	private HashMap<String, String> generateMapping(VarList[] oldVars, VarList[] newVars) {
		HashMap<String, String> mapping = new HashMap<String, String>();		
		for (int i = 0; i < oldVars.length; ++i) {
			String[] oldVarNames = oldVars[i].getIdentifiers();
			String[] newVarNames = newVars[i].getIdentifiers();
			for (int j = 0; j < oldVarNames.length; ++j) {
				mapping.put(oldVarNames[j], newVarNames[j]);
			}
		}
		return mapping;
	}
	
	// part 2, make variable names globally unique ///////////////////////////////////////////////////////////////////
	
	private void addScopePrefix() { // TODO rename
		Declaration[] oldDecls = mAstUnit.getDeclarations();
		Declaration[] newDecls = new Declaration[oldDecls.length];
		
		// Create sets of existing variable names
		HashMap<String, HashSet<String>> varIds = new HashMap<String, HashSet<String>>(oldDecls.length+1);
		HashSet<String> globalIds = new HashSet<String>();
		// Build 
		for (Declaration decl : oldDecls) {
			if (decl instanceof VariableDeclaration) {
				globalIds.addAll(varIds((VariableDeclaration) decl));
			} else if (decl instanceof Procedure) {
				Procedure d = (Procedure) decl;
				varIds.put(d.getIdentifier(), varIds(d));
			}
			// else (TypeDeclaration, Axiom, FunctionDeclaration) nothing to do?
		}
		// Create mapping of variable names for every procedure (global variables keep their name)
		HashSet<String> existingIds = new HashSet<String>(globalIds);
		HashMap<String, HashMap<String, String>> mappings = new HashMap<String, HashMap<String, String>>();
		for (String procId : varIds.keySet()) {
			HashMap<String, String> mapping = new HashMap<String, String>();
			for(String oldId : varIds.get(procId)) {
				String newId;
				int uniqueAddition = 1;
				do { // TODO increase performance by storing last uniqueAddition number
					newId = procId + "_" + oldId;
					if (uniqueAddition > 1)
						newId += "#" + uniqueAddition;
					++uniqueAddition;
				} while (existingIds.contains(newId));
				mapping.put(oldId, newId);
				existingIds.add(newId);
			}
			mappings.put(procId, mapping);
		}
		
		// Rename the variables according to the mapping
		for (int i = 0; i < oldDecls.length; ++i) {
			if (oldDecls[i] instanceof Procedure) {
				Procedure p = (Procedure) oldDecls[i];
				MappingExecutor mappingExec = new MappingExecutor(mappings.get(p.getIdentifier()));
				newDecls[i] = mappingExec.map(p);
			} else {
				newDecls[i] = oldDecls[i]; // only procedure variables are renamed
			}
		}
		mAstUnit.setDeclarations(newDecls);
	}
	
	private HashSet<String> varIds(Procedure proc) {
		HashSet<String> ids = new HashSet<String>();
		ids.addAll(varIds(proc.getInParams()));
		ids.addAll(varIds(proc.getOutParams()));
		ids.addAll(varIds(proc.getBody().getLocalVars()));
		// TODO add local variables from quantifiers (?)
		return ids;
	}
	
	private HashSet<String> varIds(VariableDeclaration... varDecls) {
		HashSet<String> ids = new HashSet<String>();
		for (VariableDeclaration varDecl : varDecls) {
			ids.addAll(varIds(varDecl.getVariables()));			
		}
		return ids;
	}
	
	private HashSet<String> varIds(VarList[] varLists) {
		HashSet<String> ids = new HashSet<String>();
		for (VarList vl : varLists) {
			for (String id : vl.getIdentifiers()) {
				ids.add(id);
			}
		}
		return ids;
	}
	
}
