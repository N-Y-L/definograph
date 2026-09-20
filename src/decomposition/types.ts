import type { Expr, TypeDescriptor } from '../core/types';
import type { TypedConstruction } from '../constructions/model';
import type { SemanticDocument, SemanticObject } from '../semantic/types';
import type { ReadingDocument } from '../reading/types';

export interface StructuralField {
  readonly name: string;
  readonly projection: string;
  readonly object: SemanticObject;
  readonly type: string;
  readonly typeExpression: Expr;
  readonly typeDescriptor?: TypeDescriptor;
  readonly kind: 'data' | 'law';
  readonly dependsOn: readonly string[];
  readonly lawDocument?: SemanticDocument;
  readonly lawReading?: ReadingDocument;
}
export interface StructuralObjectModel {
  readonly object: SemanticObject;
  readonly declarationName: string;
  readonly fields: readonly StructuralField[];
  readonly construction: TypedConstruction;
  readonly omittedFields: number;
  readonly stopReason?: string;
}
