package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class AtomicsToLocks extends BaseObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	protected AtomicsToLocks(final BoogiePreprocessorBacktranslator translator, final IUltimateServiceProvider services,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		mTranslator = translator;
		mServices = services;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
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
			final ASTType astType = new PrimitiveType(new DefaultLocation(), typeName);
			final AuxVarInfo lockVariableInfo =
					mAuxVarInfoBuilder.constructAuxVarInfo(new DefaultLocation(), astType, SFO.AUXVAR.LOCK);
			final Statement assignment = StatementFactory.constructSingleAssignmentStatement(
					lockVariableInfo.getVarDec().getLoc(), lockVariableInfo.getLhs(), new BooleanLiteral(null, false));
			final List<Declaration> newDeclarations = new ArrayList<>();
			newDeclarations.add(lockVariableInfo.getVarDec());
			Collections.addAll(newDeclarations, unit.getDeclarations());
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					final Procedure proc = (Procedure) decl;
					if (proc.getBody() != null) {
						replaceAtomics(proc);
					}
				}
			}
			return false;
		}
		return true;
	}

	private void replaceAtomics(final Procedure procedure) {

	}

}
