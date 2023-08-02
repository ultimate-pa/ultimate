/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.IExtractedWitnessEntry;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.GraphMLCorrectnessWitnessExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.YamlCorrectnessWitnessExtractor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 */
public class CACSL2BoogieTranslatorObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ACSLObjectContainerObserver mAdditionalAnnotationObserver;
	private final GraphMLCorrectnessWitnessExtractor mWitnessExtractor;
	private final YamlCorrectnessWitnessExtractor mYamlWitnessExtractor;

	private WrapperNode mRootNode;
	private ASTDecorator mInputDecorator;
	private boolean mLastModel;
	private HashRelation<IASTNode, IExtractedWitnessEntry> mWitnessInvariants;

	public CACSL2BoogieTranslatorObserver(final IUltimateServiceProvider services,
			final ACSLObjectContainerObserver additionalAnnotationObserver) {
		assert services != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mWitnessExtractor = new GraphMLCorrectnessWitnessExtractor(mServices);
		mYamlWitnessExtractor = new YamlCorrectnessWitnessExtractor(mServices);
		mAdditionalAnnotationObserver = additionalAnnotationObserver;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof WitnessNode) {
			extractWitnessInformation((WitnessNode) root);
			return false;
		}
		if (root instanceof Witness) {
			extractWitnessInformation((Witness) root);
			return false;
		}

		if ((root instanceof WrapperNode) && (((WrapperNode) root).getBacking() instanceof ASTDecorator)) {
			mInputDecorator = (ASTDecorator) ((WrapperNode) root).getBacking();
			if (mInputDecorator.countUnits() == 1) {
				final IASTTranslationUnit translationUnit = mInputDecorator.getUnit(0).getSourceTranslationUnit();
				mWitnessExtractor.setAST(translationUnit);
				mYamlWitnessExtractor.setAST(translationUnit);
			} else {
				mLogger.info("Witness extractor is disabled for multiple files");
			}
			return false;
		}

		if (root instanceof Unit) {
			throw new UnsupportedOperationException(
					"Your input file is a Boogie program. This plugin takes as input a C program.");
		}
		return false;
	}

	private void extractWitnessInformation(final Witness witness) {
		if (witness.isCorrectnessWitness()) {
			mYamlWitnessExtractor.setWitness(witness);
		}
	}

	private void extractWitnessInformation(final WitnessNode wnode) {
		final WitnessGraphAnnotation graphAnnot = WitnessGraphAnnotation.getAnnotation(wnode);

		switch (graphAnnot.getWitnessType()) {
		case VIOLATION_WITNESS:
			// is currently not handled here. May happen in the future if we want to handle assume
			break;
		case CORRECTNESS_WITNESS:
			mWitnessExtractor.setWitness(wnode);
			break;
		default:
			throw new UnsupportedOperationException("Unknown witness type " + graphAnnot.getWitnessType());
		}
	}

	@Override
	public void finish() {
		if (mWitnessExtractor.isReady()) {
			mWitnessInvariants = mWitnessExtractor.getCorrectnessWitnessInvariants();
		}
		if (mYamlWitnessExtractor.isReady()) {
			mWitnessInvariants = mYamlWitnessExtractor.getCorrectnessWitnessInvariants();
		}
		if (mLastModel) {
			if (mInputDecorator == null) {
				throw new IllegalArgumentException("There is no C AST present. Did you parse a C file?");
			}
			mRootNode = new MainTranslator(mServices, mLogger, mWitnessInvariants, mInputDecorator.getUnits(),
					mInputDecorator.getSymbolTable(), mAdditionalAnnotationObserver.getAnnotation()).getResult();
		}
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getRoot() {
		return mRootNode;
	}
}
