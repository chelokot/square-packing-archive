import {
  compiledArchiveSchema,
  type CompiledArchive,
} from "@square-packing/domain";
import archiveJson from "./generated/archive.json";

export const archive: CompiledArchive =
  compiledArchiveSchema.parse(archiveJson);
