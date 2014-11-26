package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

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
		// Store the first node of the AST and use it to process the AST manually
		if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			pickProcedures(); // TODO use
			
			// TODO
			// for every non-flat procedure p
			//     inline(p, {});
			// --------------------
			// inline(p, parents) :=
			//     if p in parents
			//         error: possible recursion!
			//     for every called procedure c in p
			//         if c is not flat
			//	           inline(c, {p} u parents)
			//         inline c into p // this changes p
			//     mark p as flat
			return false;
		}
		return true;
	}
	
	private ArrayList<Procedure> pickProcedures() {
		ArrayList<Procedure> procedures = new ArrayList<Procedure>();
		for (Declaration declaration : mAstUnit.getDeclarations()) {
			if (declaration instanceof Procedure) {
				procedures.add((Procedure) declaration);
				mLogger.error(declaration);
			}
		}
		return procedures;
	}

}
