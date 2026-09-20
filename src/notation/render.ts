import katex from 'katex';

export type TypesetResult = {status:'rendered';html:string} | {status:'unavailable';reason:string};
/** Only KaTeX-generated markup enters the UI; TeX never enables URLs, HTML, or images. */
export function typesetStatement(latex: string): TypesetResult {
  if (latex.length > 65_536) return {status:'unavailable',reason:'The mathematical notation exceeds the display limit.'};
  try {
    const html = katex.renderToString(latex, {displayMode:false,output:'htmlAndMathml',throwOnError:true,trust:false,strict:'error',maxExpand:1000,maxSize:20,macros:{}});
    return {status:'rendered',html};
  } catch {
    return {status:'unavailable',reason:'Some notation is not supported by the display renderer. The Lean statement remains available below.'};
  }
}
