package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * {@link TypeFlattener} converts types with parameters to types without
 * parameters.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class TypeFlattener extends BoogieTransformer implements IUnmanagedObserver {

	private final Logger mLogger;

	public TypeFlattener(final Logger logger) {
		mLogger = logger;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable {

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
		return true;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (!(root instanceof Unit)) {
			return true;
		}
		final Unit unit = (Unit) root;

		for (final Declaration decl : unit.getDeclarations()) {
			Declaration newDecl = processDeclaration(decl);
		}

		return false;
	}

	@Override
	protected VariableDeclaration processLocalVariableDeclaration(VariableDeclaration local) {
		return super.processLocalVariableDeclaration(local);
	}

	@Override
	protected ASTType processType(ASTType type) {
		return super.processType(type);
	}

	@Override
	protected Declaration processDeclaration(Declaration decl) {
		if (decl instanceof TypeDeclaration) {
			check((TypeDeclaration) decl);
		}
		return super.processDeclaration(decl);
	}

	private void check(TypeDeclaration typeDecl) {
		String id = typeDecl.getIdentifier();
		String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length != 0) {
			mLogger.info("Need to process " + id);
		}
	}

}
