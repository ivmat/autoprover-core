"""A minimal, dependency-free JSON Schema validator.

This implements only the subset of JSON Schema (roughly draft-07) that the
schemas in ``reference/schema/`` actually use: ``type``, ``const``,
``enum``, ``minLength``, ``pattern``, ``properties``, ``required``,
``additionalProperties``, ``items``, ``minItems``, ``allOf``, ``anyOf``,
``oneOf``, ``if``/``then``/``else``, and ``not``.

It is deliberately not a general-purpose JSON Schema engine. Extend the
keyword set here only in lockstep with something a schema file actually
needs, so the validator and the schemas never drift apart. The project
uses this instead of the third-party ``jsonschema`` package on purpose:
the reference implementation is standard-library only (see
``reference/README.md``).
"""

from __future__ import annotations

import re
from typing import Any

__all__ = ["SchemaValidationError", "iter_errors", "validate"]


class SchemaValidationError(Exception):
    """Raised when a document does not conform to a schema.

    Carries the full list of individual errors in ``.errors`` rather than
    just the first one, so a caller can see everything wrong with a
    malformed document at once.
    """

    def __init__(self, errors: list[str]):
        self.errors = list(errors)
        message = "; ".join(self.errors) if self.errors else "schema validation failed"
        super().__init__(message)


_TYPE_CHECKS = {
    "object": lambda v: isinstance(v, dict),
    "array": lambda v: isinstance(v, list),
    "string": lambda v: isinstance(v, str),
    # bool is a subtype of int in Python; JSON Schema treats booleans and
    # numbers as disjoint, so both numeric checks explicitly exclude bool.
    "number": lambda v: isinstance(v, (int, float)) and not isinstance(v, bool),
    "integer": lambda v: isinstance(v, int) and not isinstance(v, bool),
    "boolean": lambda v: isinstance(v, bool),
    "null": lambda v: v is None,
}


def _check_type(instance: Any, type_name: str) -> bool:
    try:
        return _TYPE_CHECKS[type_name](instance)
    except KeyError as exc:  # pragma: no cover - programmer error in a schema file
        raise ValueError(f"unknown JSON Schema type {type_name!r}") from exc


def iter_errors(instance: Any, schema: dict, path: str = "$") -> list[str]:
    """Return every validation error found for ``instance`` against
    ``schema``, or an empty list if it validates. Never raises on an
    invalid document — raising is ``validate``'s job.
    """
    errors: list[str] = []

    if "type" in schema:
        types = schema["type"]
        if isinstance(types, str):
            types = [types]
        if not any(_check_type(instance, t) for t in types):
            errors.append(
                f"{path}: expected type {types!r}, got {type(instance).__name__} ({instance!r})"
            )
            # Every other keyword here assumes the base type already
            # matches; checking them against a wrong-typed instance would
            # just produce confusing, redundant errors.
            return errors

    if "const" in schema and instance != schema["const"]:
        errors.append(f"{path}: expected const {schema['const']!r}, got {instance!r}")

    if "enum" in schema and instance not in schema["enum"]:
        errors.append(f"{path}: {instance!r} is not one of {schema['enum']!r}")

    if isinstance(instance, str):
        if "minLength" in schema and len(instance) < schema["minLength"]:
            errors.append(f"{path}: length {len(instance)} < minLength {schema['minLength']}")
        if "pattern" in schema and re.search(schema["pattern"], instance) is None:
            errors.append(f"{path}: {instance!r} does not match pattern {schema['pattern']!r}")

    if isinstance(instance, dict):
        properties = schema.get("properties", {})
        for key, subschema in properties.items():
            if key in instance:
                errors.extend(iter_errors(instance[key], subschema, f"{path}.{key}"))
        for required_key in schema.get("required", []):
            if required_key not in instance:
                errors.append(f"{path}: missing required property {required_key!r}")
        if schema.get("additionalProperties") is False:
            extra = sorted(set(instance) - set(properties))
            if extra:
                errors.append(f"{path}: additional properties not allowed: {extra}")

    if isinstance(instance, list):
        if "minItems" in schema and len(instance) < schema["minItems"]:
            errors.append(f"{path}: {len(instance)} items < minItems {schema['minItems']}")
        item_schema = schema.get("items")
        if item_schema is not None:
            for index, item in enumerate(instance):
                errors.extend(iter_errors(item, item_schema, f"{path}[{index}]"))

    for subschema in schema.get("allOf", []):
        errors.extend(iter_errors(instance, subschema, path))

    if "anyOf" in schema:
        branch_errors = [iter_errors(instance, s, path) for s in schema["anyOf"]]
        if not any(len(e) == 0 for e in branch_errors):
            errors.append(f"{path}: does not match any branch of anyOf")

    if "oneOf" in schema:
        branch_errors = [iter_errors(instance, s, path) for s in schema["oneOf"]]
        passing = [e for e in branch_errors if len(e) == 0]
        if len(passing) != 1:
            errors.append(
                f"{path}: matched {len(passing)} branches of oneOf, expected exactly 1"
            )

    if "not" in schema:
        if not iter_errors(instance, schema["not"], path):
            errors.append(f"{path}: must not match schema {schema['not']!r}")

    if "if" in schema:
        condition_errors = iter_errors(instance, schema["if"], path)
        if not condition_errors:
            if "then" in schema:
                errors.extend(iter_errors(instance, schema["then"], path))
        else:
            if "else" in schema:
                errors.extend(iter_errors(instance, schema["else"], path))

    return errors


def validate(instance: Any, schema: dict) -> None:
    """Validate ``instance`` against ``schema``; raise
    ``SchemaValidationError`` (never silently coerce or drop errors) if it
    does not conform.
    """
    errors = iter_errors(instance, schema)
    if errors:
        raise SchemaValidationError(errors)
