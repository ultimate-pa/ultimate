package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class CallGraphBuilder implements IUnmanagedObserver {
	
	private IUltimateServiceProvider mServices;
	
	private Unit mAstUnit;
	
	public CallGraphBuilder(IUltimateServiceProvider services) {
		mServices = services;
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
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			Unit astUnit = (Unit) root;
			BoogieProcedureFilter filter = new BoogieProcedureFilter(mServices);
			if (mServices.getProgressMonitorService().continueProcessing()) {
				scanForCallStatements(filter.getImplementations().values());
			}
			return false;
		}
		return true;
	}

	private void scanForCallStatements(Collection<Procedure> implementations) {
		for (Procedure impl : implementations) {
			scanForCallStatements(impl.getBody().getBlock());
		}
	}
	
	private void scanForCallStatements(Statement[] statements) {
		for (Statement s : statements) {
			scanForCallStatements(s);
		}
	}
	
	private void scanForCallStatements(Statement statement) {
		if (statement instanceof CallStatement) {
			
		} else if (statement instanceof IfStatement) {
			IfStatement ifStatement = (IfStatement) statement;
			scanForCallStatements(ifStatement.getThenPart());
			scanForCallStatements(ifStatement.getElsePart());
		} else if (statement instanceof WhileStatement) {
			WhileStatement whileStatement = (WhileStatement) statement;
			scanForCallStatements(whileStatement.getBody());
		}
	}
}
