// package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;
//
// import java.util.Collection;
// import java.util.HashMap;
// import java.util.Map;
//
// import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;
//
// public class ThreadInstanceState {
// private final SymmetricHashRelation<String> mActiveIfActive;
// private final Map<String, Integer> mActiveThreadInstances;
//
// public ThreadInstanceState(final Collection<String> threadNames) {
// mActiveIfActive = new SymmetricHashRelation<>();
// mActiveThreadInstances = new HashMap<>();
// threadNames.stream().forEach(t -> mActiveThreadInstances.put(t, 0));
// }
//
// public Map<String, Integer> getActiveThreadInstances() {
// return new HashMap<>(mActiveThreadInstances);
// }
//
// public SymmetricHashRelation<String> getActiveIfActive() {
// return mActiveIfActive;
// }
//
// public void update(final String forker, final String forked) {
// mActiveThreadInstances.put(forked, mActiveThreadInstances.get(forked) + 1);
// mActiveIfActive.addPair(forker, forked);
// for (final String thread : mActiveIfActive.getImage(forker)) {
// mActiveIfActive.addPair(thread, forked);
// }
// for (final String thread : mActiveIfActive.getImage(forked)) {
// mActiveIfActive.addPair(thread, forker);
// }
// }
//
// }
