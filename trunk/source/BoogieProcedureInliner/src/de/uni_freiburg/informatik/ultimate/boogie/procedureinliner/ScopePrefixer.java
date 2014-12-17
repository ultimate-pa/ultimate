package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring.MappingExecutor;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring.StringMapper;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Observer, which unites specifications and implementations of procedures
 * and gives every global variable and variable in the procedures an unique name.
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
		StringMapper mapper = new StringMapper(mapping);
		// TODO Also unite where clauses?
		// TODO keep Location and Attributes (?)
		// TODO refactor Attributes?
		return new Procedure( null, new Attribute[0], declaration.getIdentifier(),
				implementation.getTypeParams(), implementation.getInParams(), implementation.getOutParams(),
				MappingExecutor.mapVariables(declaration.getSpecification(), mapper), implementation.getBody());
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
	
	private void addScopePrefix() {
		Declaration[] oldDecls = mAstUnit.getDeclarations();
		Declaration[] newDecls = new Declaration[oldDecls.length];
		for (int i = 0; i < oldDecls.length; ++i) {
			newDecls[i] = addScopePrefix(oldDecls[i]);
		}
		// TODO when addScopePrefix(Declaration decl) implemented:
		// mAstUnit.setDeclarations(newDecls);
	}
	
	private Declaration addScopePrefix(Declaration decl) {
		// TODO implement
		if (decl instanceof TypeDeclaration) {
			// rename attributes?
			return null;
		}
		if (decl instanceof FunctionDeclaration) {
			FunctionDeclaration d = (FunctionDeclaration) decl;
			// TODO rename global variables in body
			return null;
		}
		if (decl instanceof Axiom) {
			return null;
		}
		if (decl instanceof VariableDeclaration) {
			return null;
		}
		if (decl instanceof Procedure) {
			return null;
		}
		return null;
	}
	
}
