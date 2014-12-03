package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class ProcedureInliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private Unit mAstUnit;

	public ProcedureInliner(IUltimateServiceProvider services) {
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
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		// Store the first node of the AST and use it to process the AST
		// manually
		if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			pickProcedures();

			// TODO
			// for every non-flat procedure p
			// inline(p, {});
			// --------------------
			// inline(p, parents) :=
			// if p in parents
			// error: possible recursion!
			// for every called procedure c in p
			// if c is not flat
			// inline(c, {p} u parents)
			// inline c into p // this changes p
			// mark p as flat
			return false;
		}
		return true;
	}

	private ArrayList<Procedure> pickProcedures() {
		// Filter the procedure objects from the AST
		ArrayList<Procedure> implementations = new ArrayList<Procedure>(); // implementation only
		HashMap<String, Procedure> declarations = new HashMap<String, Procedure>(); // declaration only
		ArrayList<Procedure> procedures = new ArrayList<Procedure>(); // both, implementation and declaration
		for (Declaration declaration : mAstUnit.getDeclarations()) {
			if (!(declaration instanceof Procedure))
				continue;
			Procedure p = (Procedure) declaration;
			if (p.getSpecification() == null) {
				implementations.add(p);
			} else if (p.getBody() == null) { 
				declarations.put(p.getIdentifier(), p);
			} else { 
				procedures.add(p);
			}
		}

		// Debug prints ---------------
		/*
		mLogger.error("Procedures");
		for (Procedure p : procedures)
			mLogger.warn("   " + p);
		mLogger.error("Declarations");
		for (Procedure p : declarations.values())
			mLogger.warn("   " + p);
		mLogger.error("Implementations");
		for (Procedure p : implementations)
			mLogger.error("   " + p);
		*/
		// --------------------------

		// Unite all implementations with their specifications
		for (Procedure implementation : implementations) {
			Procedure declaration = declarations.get(implementation.getIdentifier());
			if (declaration == null) {
				mLogger.error("No declaration for procedure implementation \"" + implementation.getIdentifier() + "\".");
				// TODO throw exception, using mServies
			}
			// TODO add to procedure list, remove implementation and declaration
			unite(declaration, implementation);
		}

		return procedures;
	}
	
	// Unite separate declaration and implementation of a procedure into one procedure object.
	private Procedure unite(Procedure declaration, Procedure implementation) {
		// Refactor the specification (parameters can have different names in declaration and implementation)
		Specification[] specification = new Specification[declaration.getSpecification().length];
		int i = 0;
		for (Specification s : declaration.getSpecification()) {
			if (s instanceof ModifiesSpecification) {
				specification[i] = null;				
			} else if (s instanceof RequiresSpecification) {
				// TODO refactor the expression
			} else if (s instanceof EnsuresSpecification) {
				// TODO refactor the expression
			} else {
				mLogger.error("Unexpected specification type for procedure \""
					+ declaration.getIdentifier() + "\": " + s.getClass().getName());
				// TODO: throw exception, using mServices
			}
			++i;
		}
		// Unite the procedures
		// TODO: keep values for ILocation and Attributes (?)
		return new Procedure( null, new Attribute[0], declaration.getIdentifier(),
				implementation.getTypeParams(), implementation.getInParams(), implementation.getOutParams(),
				specification, implementation.getBody());
	}
	
	// Refactor variable names inside an expression.
	// Refactoring is applied simultaneously.
	private Expression refactorVariables(Expression expr, String[] varNames, String[] newVarNames) {
		// TODO: watch out for temporary name collisions
		
		return null;
	}

}
