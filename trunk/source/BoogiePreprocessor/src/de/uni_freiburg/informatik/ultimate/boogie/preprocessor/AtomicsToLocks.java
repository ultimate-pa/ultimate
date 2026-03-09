package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class AtomicsToLocks extends BoogieTransformer implements IUnmanagedObserver {
	private static final String ULTIMATE_START = "ULTIMATE.start";

	private final BoogiePreprocessorBacktranslator mTranslator;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	protected AtomicsToLocks(final BoogiePreprocessorBacktranslator translator,
			final IUltimateServiceProvider services) {
		mTranslator = translator;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all atomic blocks and replaces them with lock-based code
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final String typeName = "bool";
			final NamedType astType = new NamedType(null, BoogieType.TYPE_BOOL, typeName, new ASTType[0]);
			final var decBuilder = new DummyVarDeclarationBuilder(astType);
			final VariableDeclaration declaration = decBuilder.getDeclaration();
			initializeLockInUnit(unit, decBuilder);
			final List<Declaration> newDeclarations = new ArrayList<>();
			newDeclarations.add(declaration);
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					Procedure proc = (Procedure) decl;
					if (proc.getBody() != null) {
						replaceAtomics(proc, declaration);
						proc = addLockToSpecification(proc, decBuilder.getLhs());
					}
					newDeclarations.add(proc);
				} else {
					newDeclarations.add(decl);
				}
			}
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			return false;
		}
		return true;
	}

	private void initializeLockInUnit(final Unit unit, final DummyVarDeclarationBuilder declarationBuilder) {
		final var numDec = unit.getDeclarations().length;
		final var declarations = Arrays.copyOf(unit.getDeclarations(), numDec);
		for (int i = 0; i < numDec; i++) {
			final Declaration decl = declarations[i];
			if (decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals(ULTIMATE_START)) {
				final var startProc = (Procedure) decl;
				final var body = startProc.getBody();
				final var block = body.getBlock();
				final var newBlock = addInitStatement(block, declarationBuilder);
				body.setBlock(newBlock);
			}
		}
	}

	private Statement[] addInitStatement(final Statement[] blockStatements,
			final DummyVarDeclarationBuilder declarationBuilder) {
		final int numStmt = blockStatements.length;
		final Statement[] newStatements = new Statement[numStmt + 1];
		final Expression falseExpression = ExpressionFactory.createBooleanLiteral(null, false);
		final LeftHandSide[] lhs = { declarationBuilder.getLhs() };
		newStatements[0] = blockStatements[0];
		newStatements[1] = StatementFactory.constructAssignmentStatement(DummyVarDeclarationBuilder.getDummyLocation(),
				lhs, new Expression[] { falseExpression });
		for (int i = 1; i < numStmt; i++) {
			newStatements[i + 1] = blockStatements[i];
		}
		return newStatements;
	}

	private Procedure addLockToSpecification(final Procedure proc, final VariableLHS lhs) {
		final var spec = proc.getSpecification();
		final var modifiesLockSpec = new ModifiesSpecification(DummyVarDeclarationBuilder.getDummyLocation(), false,
				new VariableLHS[] { lhs });
		final var newSpecification = Arrays.copyOf(spec, spec.length + 1);
		newSpecification[spec.length] = modifiesLockSpec;
		final var newProc = new Procedure(proc.getLoc(), proc.getAttributes(), proc.getIdentifier(),
				proc.getTypeParams(), proc.getInParams(), proc.getOutParams(), newSpecification, proc.getBody());
		return newProc;
	}

	private void replaceAtomics(final Procedure procedure, final VariableDeclaration lockDeclaration) {

	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {

	}

	@Override
	public void finish() {

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	private static final class DummyVarDeclarationBuilder {
		// TODO Construct unique identifier
		private static final String IDENTIFIER = "lock";
		private static BoogieType BOOL = BoogieType.TYPE_BOOL;

		private final VariableDeclaration mVariableDeclaration;
		private final ASTType mAstType;
		private final VariableLHS mLhs;

		public DummyVarDeclarationBuilder(final ASTType astType) {
			mAstType = astType;
			mVariableDeclaration = constructDeclaration();
			mLhs = setLhs(mVariableDeclaration.getLoc());
		}

		private VariableDeclaration constructDeclaration() {
			final var loc = getDummyLocation();
			return new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { IDENTIFIER }, mAstType) });
		}

		public static ILocation getDummyLocation() {
			return new DefaultLocation();
		}

		private static VariableLHS setLhs(final ILocation loc) {
			return ExpressionFactory.constructVariableLHS(loc, BOOL, IDENTIFIER,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
		}

		public VariableDeclaration getDeclaration() {
			return mVariableDeclaration;
		}

		public VariableLHS getLhs() {
			return mLhs;
		}
	}
}
