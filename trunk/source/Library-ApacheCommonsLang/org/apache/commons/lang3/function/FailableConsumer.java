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

package org.apache.commons.lang3.function;

import java.util.Objects;
import java.util.function.Consumer;

/**
 * A functional interface like {@link Consumer} that declares a {@code Throwable}.
 *
 * @param <T> Consumed type 1.
 * @param <E> Thrown exception.
 * @since 3.11
 */
@FunctionalInterface
public interface FailableConsumer<T, E extends Throwable> {

    /** NOP singleton */
    @SuppressWarnings("rawtypes")
    FailableConsumer NOP = t -> {/* NOP */};

    /**
     * Returns The NOP singleton.
     *
     * @param <T> Consumed type 1.
     * @param <E> Thrown exception.
     * @return The NOP singleton.
     */
    static <T, E extends Throwable> FailableConsumer<T, E> nop() {
        return NOP;
    }

    /**
     * Accepts the consumer.
     *
     * @param object the parameter for the consumable to accept
     * @throws E Thrown when the consumer fails.
     */
    void accept(T object) throws E;

    /**
     * Returns a composed {@code Consumer} like {@link Consumer#andThen(Consumer)}.
     *
     * @param after the operation to perform after this operation
     * @return a composed {@code Consumer} like {@link Consumer#andThen(Consumer)}.
     * @throws NullPointerException when {@code after} is null
     */
    default FailableConsumer<T, E> andThen(final FailableConsumer<? super T, E> after) {
        Objects.requireNonNull(after);
        return (final T t) -> {
            accept(t);
            after.accept(t);
        };
    }
}
