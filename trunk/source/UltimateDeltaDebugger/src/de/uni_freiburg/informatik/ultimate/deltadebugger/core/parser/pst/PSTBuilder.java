/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.List;
import java.util.Objects;
import java.util.function.Consumer;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UnbalancedConditionalDirectiveException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt.LocationResolver;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.DefaultNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTOverlappingRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.HierarchicalSourceRangeComparator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Builder to create the PST from a given AST and source code.
 */
public class PSTBuilder {
	private final ILogger mLogger;
	private final IASTTranslationUnit mTranslationUnit;
	private final ISourceDocument mSourceDocument;
	
	private IPSTNodeFactory mNodeFactory;
	
	private LocationResolver mLocationResolver;
	
	private boolean mCreateComments = true;
	
	private boolean mCreateMacroExpansions = true;
	
	private boolean mExpandConditionalBlocks = true;
	
	private ConditionalBlock mConditionalBlockRoot;
	
	private List<IPSTMacroExpansion> mMacroExpansions;
	
	private List<IPSTComment> mComments;
	
	/**
	 * Create new builder instance.
	 *
	 * @param logger
	 *            logger instance
	 * @param ast
	 *            AST instance
	 * @param sourceDocument
	 *            source document
	 */
	public PSTBuilder(final ILogger logger, final IASTTranslationUnit ast, final ISourceDocument sourceDocument) {
		mLogger = Objects.requireNonNull(logger);
		mTranslationUnit = Objects.requireNonNull(ast);
		mSourceDocument = Objects.requireNonNull(sourceDocument);
	}
	
	private static <T extends ISourceRange> IndexRange findIntersectedRanges(final List<T> ranges,
			final ISourceRange location) {
		// Find the first element that ends after the start offset,
		// all nodes before this one do not intersect
		int index = Collections.binarySearch(ranges, null,
				Comparator.comparingInt(o -> o == null ? location.offset() : o.endOffset()));
		index = index < 0 ? (-index - 1) : (index + 1);
		
		// Find the first node that starts after the location
		int endIndex = index;
		for (; endIndex != ranges.size(); ++endIndex) {
			if (ranges.get(endIndex).offset() >= location.endOffset()) {
				break;
			}
		}
		return index != endIndex ? new IndexRange(index, endIndex - 1) : null;
	}
	
	/**
	 * Throws an {@link UnbalancedConditionalDirectiveException} on unbalanced #if/#else/#endif directives.
	 * 
	 * @return new IPSTTranslationUnit instance
	 */
	public IPSTTranslationUnit build() {
		if (mLocationResolver == null) {
			mLocationResolver =
					new LocationResolver(mTranslationUnit.getContainingFilename(), mSourceDocument, mLogger);
		}
		
		if (mNodeFactory == null) {
			mNodeFactory = new DefaultNodeFactory();
		}
		
		mNodeFactory.setSourceDocument(mSourceDocument);
		
		createPreprocessorNodes();
		final IPSTTranslationUnit tu = createTree();
		insertRemainingPreprocessorNodes(tu);
		return tu;
	}
	
	private void collectRemainingPreprocessorNodes(final ConditionalBlock block, final List<IPSTNode> list) {
		block.mConditionalBlocks.stream().map(c -> c.mNode).forEachOrdered(list::add);
		list.addAll(block.mConditionalDirectives);
		list.addAll(block.mOtherDirectives);
		list.addAll(block.mIncludeDirectives);
		for (final ConditionalBlock child : block.mChildren) {
			collectRemainingPreprocessorNodes(child, list);
		}
	}
	
	private IPSTConditionalBlock createConditionalBlockNode(final List<IPSTDirective> conditionalDirectives) {
		final ISourceRange location = mSourceDocument.newSourceRange(conditionalDirectives.get(0).offset(),
				conditionalDirectives.get(conditionalDirectives.size() - 1).endOffset());
		
		ISourceRange activeBranchLocation = null;
		for (int i = 0; i < conditionalDirectives.size() - 1; ++i) {
			if (ASTNodeUtils.isConditionalPreprocessorStatementTaken(conditionalDirectives.get(i).getAstNode())) {
				activeBranchLocation = mSourceDocument.newSourceRange(conditionalDirectives.get(i).endOffset(),
						conditionalDirectives.get(i + 1).offset());
				break;
			}
		}
		
		return mNodeFactory.createConditionalBlock(location, conditionalDirectives, activeBranchLocation);
	}
	
	/**
	 * Create an intermediate tree that groups conditional preprocessor directives and the contained non-conditional
	 * directives into nodes.
	 *
	 * @return root node containing preprocessor nodes located directly in the translation unit file
	 * @throws UnbalancedConditionalDirectiveException
	 *             on unbalanced #if/#else/#endif directives
	 */
	private ConditionalBlock createConditionalBlockTree() {
		final ConditionalBlock root = new ConditionalBlock(null);
		ConditionalBlock head = root;
		
		for (final IASTPreprocessorStatement statement : mTranslationUnit.getAllPreprocessorStatements()) {
			// Skip all statements from included files
			final ISourceRange location = mLocationResolver.getSourceRangeInTranslationUnitFile(statement);
			if (location == null) {
				continue;
			}
			
			if (statement instanceof IASTPreprocessorIncludeStatement) {
				head.mIncludeDirectives.add(
						mNodeFactory.createIncludeDirective(location, (IASTPreprocessorIncludeStatement) statement));
				
				// Note that head == root should not be possible for #else and #endif directives,
				// because the parser seems to create problem nodes in these cases.
				// However, unbalanced IASTPreprocessorIf*Statement do exist, even though they
				// are not valid c.
			} else if (statement instanceof IASTPreprocessorIfStatement
					|| statement instanceof IASTPreprocessorIfdefStatement
					|| statement instanceof IASTPreprocessorIfndefStatement) {
				final ConditionalBlock newBlock = new ConditionalBlock(head);
				head = newBlock;
				head.mConditionalDirectives.add(mNodeFactory.createDirective(location, statement));
			} else if (statement instanceof IASTPreprocessorElseStatement
					|| statement instanceof IASTPreprocessorElifStatement) {
				if (head.equals(root)) {
					// should not happen
					throw new UnbalancedConditionalDirectiveException("freestanding " + statement + " at " + location);
				}
				head.mConditionalDirectives.add(mNodeFactory.createDirective(location, statement));
			} else if (statement instanceof IASTPreprocessorEndifStatement) {
				if (head.equals(root)) {
					// should not happen
					throw new UnbalancedConditionalDirectiveException("freestanding " + statement + " at " + location);
				}
				head.mConditionalDirectives.add(mNodeFactory.createDirective(location, statement));
				
				// block is complete, create real node and pop it off the stack
				head.mNode = createConditionalBlockNode(head.mConditionalDirectives);
				head.mParent.mConditionalBlocks.add(head);
				
				head.mParent.mChildren.add(head);
				head = head.mParent;
			} else {
				head.mOtherDirectives.add(mNodeFactory.createDirective(location, statement));
			}
		}
		
		if (!head.equals(root)) {
			// Does happen, but no compiler should accept this so a hard error
			// seems reasonable
			throw new UnbalancedConditionalDirectiveException("unterminated conditional directive "
					+ head.mConditionalDirectives.get(head.mConditionalDirectives.size() - 1));
		}
		
		return root;
	}
	
	private void createPreprocessorNodes() {
		mConditionalBlockRoot = createConditionalBlockTree();
		
		mMacroExpansions = new ArrayList<>();
		if (mCreateMacroExpansions) {
			for (final IASTPreprocessorMacroExpansion expansion : mTranslationUnit.getMacroExpansions()) {
				final ISourceRange location = mLocationResolver.getSourceRangeInTranslationUnitFile(expansion);
				if (location != null) {
					mMacroExpansions.add(mNodeFactory.createMacroExpansion(location, expansion));
				}
			}
		}
		
		mComments = new ArrayList<>();
		if (mCreateComments) {
			for (final IASTComment comment : mTranslationUnit.getComments()) {
				final ISourceRange location = mLocationResolver.getSourceRangeInTranslationUnitFile(comment);
				if (location != null) {
					mComments.add(mNodeFactory.createComment(location, comment));
				}
			}
		}
	}
	
	/**
	 * Copy the original AST and group nodes if they are located in an included file, a macro expansion or a conditional
	 * preprocessor block. In cases where this is not possible, because AST and preprocessor node boundaries overlap,
	 * create an overlapping node to group problematic source locations that cannot be simply rewritten.
	 */
	private IPSTTranslationUnit createTree() {
		return new TreeCreator().create();
	}
	
	/**
	 * Perform a DFS traversal and insert nodes as deep as possible. Nodes are inserted recursively, i.e. nodes are
	 * inserted into previously inserted nodes if they fit. The given list of nodes to insert must be sorted
	 * hierarchically, i.e. by start offset and larger nodes come first on same offset.
	 *
	 * @param root
	 *            node to start inserting nodes
	 * @param nodesToInsert
	 *            sorted list of nodes to insert, starting at root
	 */
	private static void insertNodesNonRecursive(final IPSTNode root, final List<IPSTNode> nodesToInsert) {
		int nextInsertIndex = 0;
		final Deque<InsertTask> stack = new ArrayDeque<>();
		stack.push(new InsertTask(root, InsertTask.ENTER, null));
		while (!stack.isEmpty() && nextInsertIndex != nodesToInsert.size()) {
			final InsertTask task = stack.peek();
			
			// Insert next node as left sibling if it starts before this node
			// and immediately process it recursively before this node
			if (task.mState == InsertTask.ENTER) {
				final IPSTNode nextToInsert = nodesToInsert.get(nextInsertIndex);
				if (nextToInsert.offset() < task.mNode.offset()) {
					conditionalInsertEnter(stack, task, nextToInsert);
					++nextInsertIndex;
					continue;
				}
				
				task.mState = InsertTask.CHILDREN;
			}
			
			// Enter next child of this node
			if (task.mState == InsertTask.CHILDREN) {
				if (task.mNextChildIndex < task.mNode.getChildren().size()) {
					stack.push(
							new InsertTask(task.mNode.getChildren().get(task.mNextChildIndex), InsertTask.ENTER, task));
					++task.mNextChildIndex;
					continue;
				}
				
				task.mState = InsertTask.LEAVE;
			}
			
			// Add everything that ends within as new child
			if (task.mState == InsertTask.LEAVE) {
				final IPSTNode nextToInsert = nodesToInsert.get(nextInsertIndex);
				if (nextToInsert.endOffset() <= task.mNode.endOffset()) {
					conditionalInsertLeave(stack, task, nextToInsert);
					++nextInsertIndex;
					continue;
				}
				stack.pop();
			}
		}
	}
	
	private static void conditionalInsertEnter(final Deque<InsertTask> stack, final InsertTask task,
			final IPSTNode nextToInsert) {
		if (!skipInsertion(task.mNode.getParent(), nextToInsert)) {
			task.mNode.getParent().addChild(task.mParentTask.mNextChildIndex - 1, nextToInsert);
			++task.mParentTask.mNextChildIndex;
			stack.push(new InsertTask(nextToInsert, InsertTask.ENTER, task.mParentTask));
		}
	}
	
	private static void conditionalInsertLeave(final Deque<InsertTask> stack, final InsertTask task,
			final IPSTNode nextToInsert) {
		if (!skipInsertion(task.mNode, nextToInsert)) {
			task.mNode.addChild(nextToInsert);
			stack.push(new InsertTask(nextToInsert, InsertTask.ENTER, task));
		}
	}
	
	private void insertRemainingPreprocessorNodes(final IPSTTranslationUnit root) {
		final List<IPSTNode> nodesToInsert = new ArrayList<>();
		collectRemainingPreprocessorNodes(mConditionalBlockRoot, nodesToInsert);
		nodesToInsert.addAll(mMacroExpansions);
		nodesToInsert.addAll(mComments);
		nodesToInsert.sort(HierarchicalSourceRangeComparator.getInstance());
		insertNodesNonRecursive(root, nodesToInsert);
	}
	
	public PSTBuilder setCreateComments(final boolean createComments) {
		mCreateComments = createComments;
		return this;
	}
	
	public PSTBuilder setCreateMacroExpansions(final boolean createMacroExpansions) {
		mCreateMacroExpansions = createMacroExpansions;
		return this;
	}
	
	public PSTBuilder setExpandConditionalBlocks(final boolean expandConditionalBlocks) {
		mExpandConditionalBlocks = expandConditionalBlocks;
		return this;
	}
	
	public PSTBuilder setNodeFactory(final IPSTNodeFactory nodeFactory) {
		mNodeFactory = nodeFactory;
		return this;
	}
	
	/**
	 * Decides if a node is inserted into a certain parent node or not. Currently only called for preprocessor nodes
	 * that do not contain ast nodes.
	 *
	 * @param parent
	 *            parent node
	 * @param node
	 *            node
	 * @return true node should not be inserted
	 */
	protected static boolean skipInsertion(final IPSTNode parent, final IPSTNode node) {
		// Only allow insertion into the active branch
		if (parent instanceof IPSTConditionalBlock) {
			return !((IPSTConditionalBlock) parent).getActiveBranchLocation().contains(node);
		}
		
		return false;
	}
	
	/**
	 * A macro expansion that cleanly maps to a single ast-node is special, because it may still contain leading or
	 * trailing tokens that belong to the parent node.
	 * This method decides if an ast-node that cleanly maps to a macro expansion is added as regular or macro expansions
	 * node.
	 *
	 * @param expansion
	 *            macro expansion
	 * @param astNode
	 *            ast node
	 * @return true if the ast-node should be added as regular node
	 */
	protected static boolean treatMacroExpansionAsRegularNode(final IPSTMacroExpansion macroExpansion,
			final IASTNode astNode) {
		// TODO: implement a better check for additional tokens and other potential problems
		// For now just check the macro definition text for a leading or trailing comma
		final String expansion = macroExpansion.getAstNode().getMacroDefinition().getExpansion();
		if (expansion.startsWith(",") || expansion.endsWith(",")) {
			return false;
		}
		
		return true;
	}
	
	/**
	 * A conditional block.
	 */
	private static class ConditionalBlock implements ISourceRange {
		private final ConditionalBlock mParent;
		private final List<ConditionalBlock> mChildren = new ArrayList<>();
		
		private IPSTConditionalBlock mNode;
		
		// List of contained nodes that still need to be inserted,
		// these lists will be modified during tree creation
		private final List<ConditionalBlock> mConditionalBlocks = new ArrayList<>();
		private final List<IPSTIncludeDirective> mIncludeDirectives = new ArrayList<>();
		private final List<IPSTDirective> mConditionalDirectives = new ArrayList<>();
		private final List<IPSTDirective> mOtherDirectives = new ArrayList<>();
		
		ConditionalBlock(final ConditionalBlock parent) {
			mParent = parent;
		}
		
		@Override
		public int endOffset() {
			return mNode.endOffset();
		}
		
		@Override
		public int offset() {
			return mNode.offset();
		}
	}
	
	/**
	 * Creates a task for children.
	 */
	private static class CreateChildrenTask {
		private final IPSTNode mNode;
		private final List<IASTNode> mChildren;
		private final ConditionalBlock mContext;
		private final CreateChildrenTask mNext;
		
		CreateChildrenTask(final IPSTNode node, final List<IASTNode> children, final ConditionalBlock context,
				final CreateChildrenTask next) {
			mNode = node;
			mChildren = children;
			mContext = context;
			mNext = next;
		}
	}
	
	/**
	 * The range of an index.
	 */
	private static class IndexRange {
		private final int mFirst; // inclusive
		private final int mLast; // inclusive
		
		public IndexRange(final int first, final int last) {
			mFirst = first;
			mLast = last;
		}
	}
	
	/**
	 * A task for insertion.
	 */
	private static class InsertTask {
		public static final int ENTER = 0;
		public static final int CHILDREN = 1;
		public static final int LEAVE = 2;
		
		private final IPSTNode mNode;
		private int mState;
		private int mNextChildIndex;
		private final InsertTask mParentTask;
		
		InsertTask(final IPSTNode node, final int state, final InsertTask parentTask) {
			mNode = node;
			mState = state;
			mNextChildIndex = 0;
			mParentTask = parentTask;
		}
	}
	
	/**
	 * A group of overlapping siblings.
	 */
	private static class OverlappingSiblingsGroup implements ISourceRange {
		private final List<IASTNode> mNodes = new ArrayList<>();
		private final int mOffset;
		private int mEndOffset;
		private int mFirstConditionalBlockIndex = -1;
		
		OverlappingSiblingsGroup(final ISourceRange location) {
			mOffset = location.offset();
			mEndOffset = location.endOffset();
		}
		
		@Override
		public int endOffset() {
			return mEndOffset;
		}
		
		@Override
		public int offset() {
			return mOffset;
		}
	}
	
	/**
	 * Creates a tree.
	 */
	class TreeCreator {
		private CreateChildrenTask mStack;
		
		void addConditionalBlock(final IPSTNode parent, final List<IASTNode> unexpandedChildren,
				final ConditionalBlock block) {
			parent.addChild(block.mNode);
			if (mExpandConditionalBlocks) {
				pushTask(block.mNode, unexpandedChildren, block);
			} else {
				block.mNode.setUnexpandedChildNodes(unexpandedChildren);
			}
		}
		
		void addMacroExpansionAsRegularNode(final IPSTNode parent, final IPSTMacroExpansion macroExpansion,
				final IASTNode astNode) {
			final IPSTRegularNode node = mNodeFactory.createRegularNode(macroExpansion, astNode);
			parent.addChild(node);
			macroExpansion.setUnexpandedChildNodes(Arrays.asList(astNode.getChildren()));
			node.addChild(macroExpansion);
		}
		
		void addOverlappingNode(final IPSTNode parent, final OverlappingSiblingsGroup group) {
			final IPSTOverlappingRegion node = mNodeFactory.createOverlappingRegion(group);
			node.setUnexpandedChildNodes(group.mNodes);
			parent.addChild(node);
		}
		
		void addPreprocessorNode(final IPSTNode parent, final List<IASTNode> unexpandedChildren, final IPSTNode node) {
			node.setUnexpandedChildNodes(unexpandedChildren);
			parent.addChild(node);
		}
		
		void addRegularNode(final IPSTNode parent, final OverlappingSiblingsGroup group,
				final ConditionalBlock context) {
			final IASTNode astNode = group.mNodes.get(0);
			final IPSTRegularNode node = mNodeFactory.createRegularNode(group, astNode);
			parent.addChild(node);
			pushTask(node, Arrays.asList(astNode.getChildren()), context);
		}
		
		IPSTTranslationUnit create() {
			final IPSTTranslationUnit root = mNodeFactory.createTranslationUnit(
					mLocationResolver.getSourceRangeInTranslationUnitFile(mTranslationUnit), mTranslationUnit);
			pushTask(root, Arrays.asList(mTranslationUnit.getChildren()), mConditionalBlockRoot);
			while (mStack != null) {
				final CreateChildrenTask task = mStack;
				mStack = mStack.mNext;
				groupOverlappingSiblings(task.mChildren, task.mContext.mConditionalBlocks,
						group -> createChildForGroup(task.mNode, group, task.mContext));
			}
			
			return root;
		}
		
		void createChildForGroup(final IPSTNode node, final OverlappingSiblingsGroup group,
				final ConditionalBlock context) {
			// Check if this is a conditional block
			if (group.mFirstConditionalBlockIndex != -1) {
				// There may be multiple expansions, check if the expanded location matches
				// the block before creating a conditional block node for this group
				// If it doesn't there are overlapping nodes and/or multiple blocks
				final ConditionalBlock block = context.mConditionalBlocks.get(group.mFirstConditionalBlockIndex);
				if (group.equalsSourceRange(block.mNode)) {
					context.mConditionalBlocks.remove(group.mFirstConditionalBlockIndex);
					addConditionalBlock(node, group.mNodes, block);
				} else {
					addOverlappingNode(node, group);
				}
				return;
			}
			
			// Check if it's an include
			int index = findEqualRange(context.mIncludeDirectives, group);
			if (index != -1) {
				addPreprocessorNode(node, group.mNodes, context.mIncludeDirectives.remove(index));
				return;
			}
			
			// Check if it's a macro expansion
			// Certain macro expansions that cleanly map to astnodes may be added as regular nodes
			// with the macro expansion as only child
			index = findEqualRange(mMacroExpansions, group);
			if (index != -1) {
				final IPSTMacroExpansion macroExpansion = mMacroExpansions.remove(index);
				if (group.mNodes.size() == 1 && treatMacroExpansionAsRegularNode(macroExpansion, group.mNodes.get(0))) {
					addMacroExpansionAsRegularNode(node, macroExpansion, group.mNodes.get(0));
					return;
				}
				
				addPreprocessorNode(node, group.mNodes, macroExpansion);
				return;
			}
			
			// It's a regular node if there is only a single node at this location
			if (group.mNodes.size() == 1) {
				addRegularNode(node, group, context);
				return;
			}
			
			// Otherwise group the nodes at this location into an overlapping block node
			// and just leave this mess alone
			addOverlappingNode(node, group);
		}
		
		void pushTask(final IPSTNode node, final List<IASTNode> children, final ConditionalBlock context) {
			mStack = new CreateChildrenTask(node, children, context, mStack);
		}
		
		/**
		 * Find siblings that overlap the same source location and thus cannot be added as siblings. The common case are
		 * macro expansions and includes, but this method also groups nodes within conditional preprocessor blocks in
		 * order to detect nodes that overlap #ifdef/#endif directives
		 *
		 * @param siblings
		 *            libst of siblings
		 * @param conditionalBlocks
		 *            list of conditional blocks
		 * @param consumer
		 *            consumer
		 */
		private void groupOverlappingSiblings(final List<IASTNode> siblings,
				final List<? extends ISourceRange> conditionalBlocks,
				final Consumer<OverlappingSiblingsGroup> consumer) {
			OverlappingSiblingsGroup currentGroup = null;
			for (final IASTNode node : siblings) {
				// Map the node location to the translation unit file and skip nodes that do not
				// span any characters (e.g. implicit names)
				ISourceRange location = mLocationResolver.getSourceRangeMappedToInclusionStatement(node);
				if (location == null || location.length() == 0) {
					continue;
				}
				
				// Immediately add node to current group if it fits inside
				if (currentGroup != null && currentGroup.contains(location)) {
					currentGroup.mNodes.add(node);
					continue;
				}
				
				// Expand the location to include enclosing conditional blocks
				int firstConditionalBlockIndex = -1;
				final IndexRange intersectedBlocks = findIntersectedRanges(conditionalBlocks, location);
				if (intersectedBlocks != null) {
					// Expand the location to include all blocks that have been found,
					// but ignore fully contained blocks
					final ISourceRange expandedLocation = mSourceDocument.newSourceRange(
							Math.min(location.offset(), conditionalBlocks.get(intersectedBlocks.mFirst).offset()),
							Math.max(location.endOffset(), conditionalBlocks.get(intersectedBlocks.mLast).endOffset()));
					if (expandedLocation.offset() != location.offset()
							|| expandedLocation.endOffset() != location.endOffset()) {
						firstConditionalBlockIndex = intersectedBlocks.mFirst;
						location = expandedLocation;
					}
				}
				
				if (currentGroup == null || location.offset() >= currentGroup.mEndOffset) {
					// Complete the current group and create a new one for this location
					if (currentGroup != null) {
						consumer.accept(currentGroup);
					}
					currentGroup = new OverlappingSiblingsGroup(location);
				} else {
					// Expand the current group
					currentGroup.mEndOffset = location.endOffset();
				}
				
				currentGroup.mNodes.add(node);
				if (firstConditionalBlockIndex != -1 && currentGroup.mFirstConditionalBlockIndex == -1) {
					currentGroup.mFirstConditionalBlockIndex = firstConditionalBlockIndex;
				}
			}
			
			if (currentGroup != null) {
				consumer.accept(currentGroup);
			}
		}
		
		private <T extends ISourceRange> int findEqualRange(final List<T> ranges, final ISourceRange location) {
			final int index = Collections.binarySearch(ranges, location, Comparator.comparingInt(ISourceRange::offset));
			if (index >= 0 && ranges.get(index).endOffset() == location.endOffset()) {
				return index;
			}
			return -1;
		}
	}
}
