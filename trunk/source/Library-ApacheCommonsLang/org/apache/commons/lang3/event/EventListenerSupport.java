/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.commons.lang3.event;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.Array;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import org.apache.commons.lang3.Validate;

/**
 * <p>An EventListenerSupport object can be used to manage a list of event
 * listeners of a particular type. The class provides
 * {@link #addListener(Object)} and {@link #removeListener(Object)} methods
 * for registering listeners, as well as a {@link #fire()} method for firing
 * events to the listeners.
 * </p>
 *
 * <p>
 * To use this class, suppose you want to support ActionEvents.  You would do:
 * </p>
 * <pre><code>
 * public class MyActionEventSource
 * {
 *   private EventListenerSupport&lt;ActionListener&gt; actionListeners =
 *       EventListenerSupport.create(ActionListener.class);
 *
 *   public void someMethodThatFiresAction()
 *   {
 *     ActionEvent e = new ActionEvent(this, ActionEvent.ACTION_PERFORMED, "somethingCool");
 *     actionListeners.fire().actionPerformed(e);
 *   }
 * }
 * </code></pre>
 *
 * <p>
 * Serializing an {@link EventListenerSupport} instance will result in any
 * non-{@link Serializable} listeners being silently dropped.
 * </p>
 *
 * @param <L> the type of event listener that is supported by this proxy.
 *
 * @since 3.0
 */
public class EventListenerSupport<L> implements Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 3593265990380473632L;

    /**
     * The list used to hold the registered listeners. This list is
     * intentionally a thread-safe copy-on-write-array so that traversals over
     * the list of listeners will be atomic.
     */
    private List<L> listeners = new CopyOnWriteArrayList<>();

    /**
     * The proxy representing the collection of listeners. Calls to this proxy
     * object will sent to all registered listeners.
     */
    private transient L proxy;

    /**
     * Empty typed array for #getListeners().
     */
    private transient L[] prototypeArray;

    /**
     * Creates an EventListenerSupport object which supports the specified
     * listener type.
     *
     * @param <T> the type of the listener interface
     * @param listenerInterface the type of listener interface that will receive
     *        events posted using this class.
     *
     * @return an EventListenerSupport object which supports the specified
     *         listener type.
     *
     * @throws NullPointerException if {@code listenerInterface} is
     *         {@code null}.
     * @throws IllegalArgumentException if {@code listenerInterface} is
     *         not an interface.
     */
    public static <T> EventListenerSupport<T> create(final Class<T> listenerInterface) {
        return new EventListenerSupport<>(listenerInterface);
    }

    /**
     * Creates an EventListenerSupport object which supports the provided
     * listener interface.
     *
     * @param listenerInterface the type of listener interface that will receive
     *        events posted using this class.
     *
     * @throws NullPointerException if {@code listenerInterface} is
     *         {@code null}.
     * @throws IllegalArgumentException if {@code listenerInterface} is
     *         not an interface.
     */
    public EventListenerSupport(final Class<L> listenerInterface) {
        this(listenerInterface, Thread.currentThread().getContextClassLoader());
    }

    /**
     * Creates an EventListenerSupport object which supports the provided
     * listener interface using the specified class loader to create the JDK
     * dynamic proxy.
     *
     * @param listenerInterface the listener interface.
     * @param classLoader       the class loader.
     *
     * @throws NullPointerException if {@code listenerInterface} or
     *         {@code classLoader} is {@code null}.
     * @throws IllegalArgumentException if {@code listenerInterface} is
     *         not an interface.
     */
    public EventListenerSupport(final Class<L> listenerInterface, final ClassLoader classLoader) {
        this();
        Validate.notNull(listenerInterface, "listenerInterface");
        Validate.notNull(classLoader, "classLoader");
        Validate.isTrue(listenerInterface.isInterface(), "Class %s is not an interface",
                listenerInterface.getName());
        initializeTransientFields(listenerInterface, classLoader);
    }

    /**
     * Create a new EventListenerSupport instance.
     * Serialization-friendly constructor.
     */
    private EventListenerSupport() {
    }

    /**
     * Returns a proxy object which can be used to call listener methods on all
     * of the registered event listeners. All calls made to this proxy will be
     * forwarded to all registered listeners.
     *
     * @return a proxy object which can be used to call listener methods on all
     * of the registered event listeners
     */
    public L fire() {
        return proxy;
    }

//**********************************************************************************************************************
// Other Methods
//**********************************************************************************************************************

    /**
     * Registers an event listener.
     *
     * @param listener the event listener (may not be {@code null}).
     *
     * @throws NullPointerException if {@code listener} is
     *         {@code null}.
     */
    public void addListener(final L listener) {
        addListener(listener, true);
    }

    /**
     * Registers an event listener.  Will not add a pre-existing listener
     * object to the list if {@code allowDuplicate} is false.
     *
     * @param listener the event listener (may not be {@code null}).
     * @param allowDuplicate the flag for determining if duplicate listener
     * objects are allowed to be registered.
     *
     * @throws NullPointerException if {@code listener} is {@code null}.
     * @since 3.5
     */
    public void addListener(final L listener, final boolean allowDuplicate) {
        Validate.notNull(listener, "listener");
        if (allowDuplicate || !listeners.contains(listener)) {
            listeners.add(listener);
        }
    }

    /**
     * Returns the number of registered listeners.
     *
     * @return the number of registered listeners.
     */
    int getListenerCount() {
        return listeners.size();
    }

    /**
     * Unregisters an event listener.
     *
     * @param listener the event listener (may not be {@code null}).
     *
     * @throws NullPointerException if {@code listener} is
     *         {@code null}.
     */
    public void removeListener(final L listener) {
        Validate.notNull(listener, "listener");
        listeners.remove(listener);
    }

    /**
     * Gets an array containing the currently registered listeners.
     * Modification to this array's elements will have no effect on the
     * {@link EventListenerSupport} instance.
     * @return L[]
     */
    public L[] getListeners() {
        return listeners.toArray(prototypeArray);
    }

    /**
     * Serialize.
     * @param objectOutputStream the output stream
     * @throws IOException if an IO error occurs
     */
    private void writeObject(final ObjectOutputStream objectOutputStream) throws IOException {
        final ArrayList<L> serializableListeners = new ArrayList<>();

        // don't just rely on instanceof Serializable:
        ObjectOutputStream testObjectOutputStream = new ObjectOutputStream(new ByteArrayOutputStream());
        for (final L listener : listeners) {
            try {
                testObjectOutputStream.writeObject(listener);
                serializableListeners.add(listener);
            } catch (final IOException exception) {
                //recreate test stream in case of indeterminate state
                testObjectOutputStream = new ObjectOutputStream(new ByteArrayOutputStream());
            }
        }
        /*
         * we can reconstitute everything we need from an array of our listeners,
         * which has the additional advantage of typically requiring less storage than a list:
         */
        objectOutputStream.writeObject(serializableListeners.toArray(prototypeArray));
    }

    /**
     * Deserialize.
     * @param objectInputStream the input stream
     * @throws IOException if an IO error occurs
     * @throws ClassNotFoundException if the class cannot be resolved
     */
    private void readObject(final ObjectInputStream objectInputStream) throws IOException, ClassNotFoundException {
        @SuppressWarnings("unchecked") // Will throw CCE here if not correct
        final
        L[] srcListeners = (L[]) objectInputStream.readObject();

        this.listeners = new CopyOnWriteArrayList<>(srcListeners);

        @SuppressWarnings("unchecked") // Will throw CCE here if not correct
        final
        Class<L> listenerInterface = (Class<L>) srcListeners.getClass().getComponentType();

        initializeTransientFields(listenerInterface, Thread.currentThread().getContextClassLoader());
    }

    /**
     * Initialize transient fields.
     * @param listenerInterface the class of the listener interface
     * @param classLoader the class loader to be used
     */
    private void initializeTransientFields(final Class<L> listenerInterface, final ClassLoader classLoader) {
        @SuppressWarnings("unchecked") // Will throw CCE here if not correct
        final
        L[] array = (L[]) Array.newInstance(listenerInterface, 0);
        this.prototypeArray = array;
        createProxy(listenerInterface, classLoader);
    }

    /**
     * Create the proxy object.
     * @param listenerInterface the class of the listener interface
     * @param classLoader the class loader to be used
     */
    private void createProxy(final Class<L> listenerInterface, final ClassLoader classLoader) {
        proxy = listenerInterface.cast(Proxy.newProxyInstance(classLoader,
                new Class[] { listenerInterface }, createInvocationHandler()));
    }

    /**
     * Create the {@link InvocationHandler} responsible for broadcasting calls
     * to the managed listeners.  Subclasses can override to provide custom behavior.
     * @return ProxyInvocationHandler
     */
    protected InvocationHandler createInvocationHandler() {
        return new ProxyInvocationHandler();
    }

    /**
     * An invocation handler used to dispatch the event(s) to all the listeners.
     */
    protected class ProxyInvocationHandler implements InvocationHandler {

        /**
         * Propagates the method call to all registered listeners in place of
         * the proxy listener object.
         *
         * @param unusedProxy the proxy object representing a listener on which the
         *        invocation was called; not used
         * @param method the listener method that will be called on all of the
         *        listeners.
         * @param args event arguments to propagate to the listeners.
         * @return the result of the method call
         * @throws Throwable if an error occurs
         */
        @Override
        public Object invoke(final Object unusedProxy, final Method method, final Object[] args) throws Throwable {
            for (final L listener : listeners) {
                method.invoke(listener, args);
            }
            return null;
        }
    }
}
