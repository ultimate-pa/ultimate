/*
 * Copyright (C) 2009-2015 Björn Buchhold
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
/*
� * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	PersistenceAwareModelManager.java created on Nov 11, 2009 by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.DataAccessException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.PersistentObjectTypeMismatchException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.modelrepository.IRepository;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.modelrepository.SerializationRepository;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * PersistenceAwareModelManager
 *
 * Standard implementation of the {@link IModelManager} A {@link PersistenceAwareModelManager} is created using a
 * repository. The default repository is the System's java temporary directory. There should be a property page to set
 * the repository's location in the file system to a desired value
 *
 * The ModelManager should be used for any access to models produced by previous tool runs.
 *
 * The Application may ask the ModelManager to persist and models and probably drop them from the in-memory map.
 * Subsequent access to such a model is dispatched to the repository and the model is added to the memory-map, again
 *
 * @author Björn Buchhold
 *
 */
public class PersistenceAwareModelManager implements IModelManager {

	private final LinkedHashMap<ModelType, ModelContainer> mModelMap;
	private final IRepository<String, ModelContainer> mRepository;
	private final ILogger mLogger;
	private ModelType mLastAdded;

	public PersistenceAwareModelManager(final File repositoryRoot, final ILogger logger) {
		assert logger != null;
		mModelMap = new LinkedHashMap<>();
		mLogger = logger;
		mLogger.info("Repository-Root is: " + repositoryRoot.getAbsolutePath());
		mRepository = new SerializationRepository(repositoryRoot, mLogger);
	}

	public PersistenceAwareModelManager(final String tmpDir, final ILogger logger) {
		this(new File(tmpDir), logger);
	}

	/**
	 * String createFileNameFromNode
	 *
	 * @param node
	 * @return File name for a given node.
	 */
	private static String createFileNameFromNode(final IElement node) {
		if (node == null) {
			return "";
		}
		String graphName = "";
		final ILocation loc = ILocation.getAnnotation(node);
		if (loc != null && loc.getFileName() != null) {
			graphName = loc.getFileName();
		}
		if (graphName.contains(", ")) {
			final String fileSep = ", ";
			final String[] names = graphName.split(fileSep);
			final StringBuilder sb = new StringBuilder();
			for (final String s : names) {
				sb.append(s.substring(s.lastIndexOf(File.separator) + 1)).append(fileSep);
			}
			graphName = sb.delete(sb.length() - 2, sb.length()).toString();
		} else {
			graphName = graphName.trim();
			graphName = graphName.substring(graphName.lastIndexOf(File.separator) + 1);
		}
		return graphName;
	}

	/**
	 * Adds a new container to the in-memory model store.
	 *
	 * @param container
	 * @return false if model is present in the in-memory store, true otherwise
	 */
	private boolean addItem(final ModelContainer container) {
		final ModelType type = container.getType();
		if (mModelMap.containsKey(type)) {
			mLogger.warn("Model is already present, skipping insertion....");
			return false;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Inserting " + container);
		}
		mModelMap.put(type, container);
		mLastAdded = type;
		return true;
	}

	/**
	 * Adds a new model to the in-memory model store.
	 *
	 * @param rootNode
	 *            The model represented by an {@link IElement}.
	 * @param graphtype
	 *            The {@link ModelType} of the model
	 * @return false if this model is already in the in-memory store, true otherwise
	 */
	@Override
	public boolean addItem(final IElement rootNode, final ModelType graphtype) {
		return addItem(new ModelContainer(rootNode, graphtype, createFileNameFromNode(rootNode)));
	}

	@Override
	public List<String> getItemNames() {
		final List<String> names = new ArrayList<>();
		for (final ModelType t : mModelMap.keySet()) {
			names.add(t.toString());
		}
		names.addAll(mRepository.listKeys());
		return names;
	}

	@Override
	public ModelType getLastAdded() {
		return mLastAdded;
	}

	@Override
	public IElement getRootNode(final ModelType graph) throws GraphNotFoundException {
		ModelContainer container = mModelMap.get(graph);
		if (container == null) {
			try {
				container = mRepository.get(graph.toString());
				mModelMap.put(graph, container);
			} catch (final PersistentObjectNotFoundException e) {
				throw new GraphNotFoundException(graph, e);
			} catch (final PersistentObjectTypeMismatchException e) {
				mLogger.error("Could not deserialize graph " + graph, e);
				throw new GraphNotFoundException(graph, e);
			}
		}
		return container.getRoot();
	}

	@Override
	public boolean isEmpty() {
		return mModelMap.isEmpty() && mRepository.isEmpty();
	}

	@Override
	public void persistAll(final boolean keepInMemory) throws StoreObjectException {
		for (final Entry<ModelType, ModelContainer> mapEntry : mModelMap.entrySet()) {
			if (mapEntry.getKey() == null || mapEntry.getValue() == null) {
				continue;
			}
			mRepository.addOrReplace(mapEntry.getKey().toString(), mapEntry.getValue());
		}
		if (!keepInMemory) {
			removeAll();
		}
	}

	@Override
	public void persistAndDropExistingGraph(final ModelType key) throws StoreObjectException, GraphNotFoundException {
		persistExistingGraph(key, false);
	}

	@Override
	public void persistExistingGraph(final ModelType key, final boolean keepInMemory)
			throws StoreObjectException, GraphNotFoundException {
		if (mModelMap.containsKey(key)) {
			mRepository.addOrReplace(key.toString(), mModelMap.get(key));
			if (!keepInMemory) {
				mModelMap.remove(key);
			}
		} else {
			throw new GraphNotFoundException(key);
		}

	}

	@Override
	public void removeAll() {
		mModelMap.clear();
	}

	@Override
	public boolean removeItem(final ModelType graphtype) {
		boolean successfull = true;
		if (mModelMap.containsKey(graphtype)) {
			successfull = mModelMap.remove(graphtype) != null;
		}
		return successfull && mRepository.remove(graphtype.toString());
	}

	@Override
	public boolean removeItem(final String id) {
		boolean successfull = true;
		final ModelType graphType = getInMemoryGraphTypeById(id);
		if (graphType != null) {
			successfull = mModelMap.remove(graphType) != null;
		}
		return successfull && mRepository.remove(id);
	}

	@Override
	public boolean removeItem(final ModelContainer vault) {
		return mModelMap.remove(vault.getType()) != null;
	}

	@Override
	public ModelType getGraphTypeById(final String s) {
		for (final ModelType t : mModelMap.keySet()) {
			if (t.toString().equals(s)) {
				return t;
			}
		}
		if (mRepository.listKeys().contains(s)) {
			try {
				return mRepository.get(s).getType();
			} catch (final DataAccessException e) {
				mLogger.error("Problems deserializing persistent model: ", e);
			}
		}
		return null;
	}

	private ModelType getInMemoryGraphTypeById(final String id) {
		for (final ModelType t : mModelMap.keySet()) {
			if (t.toString().equals(id)) {
				return t;
			}
		}
		return null;
	}

	@Override
	public ModelType getGraphTypeByGeneratorPluginId(final String id) {
		final Optional<Entry<ModelType, ModelContainer>> creator =
				mModelMap.entrySet().stream().filter(a -> a.getKey().getCreator().equals(id)).findFirst();
		if (creator.isPresent()) {
			return creator.get().getKey();
		}

		for (final String keyFromRepos : mRepository.listKeys()) {
			if (keyFromRepos.contains(id)) {
				try {
					final ModelType graphType = mRepository.get(keyFromRepos).getType();
					if (graphType.getCreator().equals(id)) {
						return graphType;
					}
				} catch (final DataAccessException e) {
					mLogger.error("Problems deserializing persistent model: ", e);
				}
			}
		}
		return null;
	}

	@Override
	public int size() {
		mLogger.debug("Current MM size is " + mModelMap.size() + ". There are " + mRepository.listKeys().size()
				+ " models in the repository.");
		return mModelMap.size();
	}

	@Override
	public List<ModelType> getItemKeys() {
		return new ArrayList<>(mModelMap.keySet());
	}
}
