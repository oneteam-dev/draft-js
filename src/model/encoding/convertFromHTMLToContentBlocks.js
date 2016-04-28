/**
 * Copyright (c) 2013-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 * @providesModule convertFromHTMLToContentBlocks
 * @typechecks
 * @flow
 */

'use strict';

const CharacterMetadata = require('CharacterMetadata');
const ContentBlock = require('ContentBlock');
const DraftEntity = require('DraftEntity');
const Immutable = require('immutable');
const URI = require('URI');

const generateRandomKey = require('generateRandomKey');
const getSafeBodyFromHTML = require('getSafeBodyFromHTML');
const invariant = require('invariant');
const nullthrows = require('nullthrows');
const sanitizeDraftText = require('sanitizeDraftText');

import type {DraftBlockType} from 'DraftBlockType';
import type {DraftInlineStyle} from 'DraftInlineStyle';

var {
  List,
  OrderedSet,
} = Immutable;

var NBSP = '&nbsp;';
var SPACE = ' ';

// Arbitrary max indent
var MAX_DEPTH = 4;

// used for replacing characters in HTML
var REGEX_CR = new RegExp('\r', 'g');
var REGEX_LF = new RegExp('\n', 'g');
var REGEX_NBSP = new RegExp(NBSP, 'g');

// Block tag flow is different because LIs do not have
// a deterministic style ;_;
var blockTags = ['p', 'h1', 'h2', 'h3', 'h4', 'h5', 'li', 'blockquote', 'pre', 'div'];
var inlineTags = {
  b: 'BOLD',
  code: 'CODE',
  del: 'STRIKETHROUGH',
  em: 'ITALIC',
  i: 'ITALIC',
  s: 'STRIKETHROUGH',
  strike: 'STRIKETHROUGH',
  strong: 'BOLD',
  u: 'UNDERLINE',
};
var MEDIA = {
  img: 'IMAGE',
  video: 'VIDEO',
  audio: 'AUDIO'
};
var IFRAME = 'IFRAME';

// https://github.com/quilljs/quill/
var OLD_COLORS = [
  'rgb(0, 0, 0)', 'rgb(230, 0, 0)', 'rgb(255, 153, 0)', 'rgb(255, 255, 0)',
  'rgb(0, 138, 0)', 'rgb(0, 102, 204)', 'rgb(153, 51, 255)', 'rgb(255, 255, 255)',
  'rgb(250, 204, 204)', 'rgb(255, 235, 204)', 'rgb(255, 255, 204)', 'rgb(204, 232, 204)',
  'rgb(204, 224, 245)', 'rgb(235, 214, 255)', 'rgb(187, 187, 187)', 'rgb(240, 102, 102)',
  'rgb(255, 194, 102)', 'rgb(255, 255, 102)', 'rgb(102, 185, 102)', 'rgb(102, 163, 224)',
  'rgb(194, 133, 255)', 'rgb(136, 136, 136)', 'rgb(161, 0, 0)', 'rgb(178, 107, 0)',
  'rgb(178, 178, 0)', 'rgb(0, 97, 0)', 'rgb(0, 71, 178)', 'rgb(107, 36, 178)',
  'rgb(68, 68, 68)', 'rgb(92, 0, 0)', 'rgb(102, 61, 0)', 'rgb(102, 102, 0)',
  'rgb(0, 55, 0)', 'rgb(0, 41, 102)', 'rgb(61, 20, 10)',
];
var OLD_INLINE_STYLES_SIZE = {
  SIZE_NORMAL: { fontSize: 13 },
  SIZE_SMALLER: { fontSize: 10 },
  SIZE_LARGER: { fontSize: 24 },
  SIZE_HUGE: { fontSize: 32 },
};
var OLD_INLINE_STYLES = OLD_COLORS.reduce((result, color, i) => {
  result[`COLOR${i}`] = { color };
  result[`BACKGROUND_COLOR${i}`] = { backgroundColor: color };
  return result;
}, OLD_INLINE_STYLES_SIZE);
var OLD_BLOCK_TYPES = {
  ALIGN_CENTER: 'align-center',
  ALIGN_RIGHT: 'align-right',
  ALIGN_JUSTIFY: 'align-justify',
};

var lastBlock;

type Block = {
  type: DraftBlockType;
  depth: number;
};

type Chunk = {
  text: string;
  inlines: Array<DraftInlineStyle>;
  entities: Array<string>;
  blocks: Array<Block>;
};

function getEmptyChunk(): Chunk {
  return {
    text: '',
    inlines: [],
    entities: [],
    blocks: [],
  };
}

function getWhitespaceChunk(inEntity: ?string): Chunk {
  var entities = new Array(1);
  if (inEntity) {
    entities[0] = inEntity;
  }
  return {
    text: SPACE,
    inlines: [OrderedSet()],
    entities,
    blocks: [],
  };
}

function getSoftNewlineChunk(): Chunk {
  return {
    text: '\n',
    inlines: [OrderedSet()],
    entities: new Array(1),
    blocks: [],
  };
}

function hasInputTypeCheckbox(node: ?Node): boolean {
  if (!node || !node.children) { return false; }
  return node.children[0].tagName.toLowerCase() === 'input' &&
    node.children[0].type === 'checkbox';
}

function getBlockDividerChunk(block: DraftBlockType, depth: number, node: ?Node): Chunk {
  var chunk = {
    text: '\r',
    inlines: [OrderedSet()],
    entities: new Array(1),
    blocks: [{
      type: block,
      depth: Math.max(0, Math.min(MAX_DEPTH, depth)),
    }],
  };
  if (block === 'checkable-list-item' && hasInputTypeCheckbox(node)) {
    chunk.blocks[0].checked = node.children[0].checked ? true : false;
  }
  return chunk;
}

function getBlockTypeForTag(tag: string, lastList: ?string, node: ?Node): DraftBlockType {
  switch (tag) {
    case 'h1':
      return 'header-one';
    case 'h2':
      return 'header-two';
    case 'h3':
      return 'header-three';
    case 'h4':
      return 'header-four';
    case 'h5':
      return 'header-five';
    case 'h6':
      return 'header-six';
    case 'li':
      if (lastList === 'ol') {
        return 'ordered-list-item';
      }
      if (node.classList.contains('task-list-item')) {
        return 'checkable-list-item';
      }
      return 'unordered-list-item';
    case 'blockquote':
      return 'blockquote';
    case 'pre':
      return 'code-block';
    case 'div':
      if (node.style.textAlign === 'center') {
        return OLD_BLOCK_TYPES.ALIGN_CENTER;
      } else if (node.style.textAlign === 'right') {
        return OLD_BLOCK_TYPES.ALIGN_RIGHT;
      } else if (node.style.textAlign === 'justify') {
        return OLD_BLOCK_TYPES.ALIGN_JUSTIFY;
      } else {
        return 'unstyled';
      }
    default:
      return 'unstyled';
  }
}

function hasOldStyleFontSize(node: Node): boolean {
  return Object.keys(OLD_INLINE_STYLES_SIZE).some(label => (
    OLD_INLINE_STYLES_SIZE[label].fontSize === parseInt(node.style.fontSize, 10)
  ));
}

function hasOldStyleColor(node: Node, prop: string): boolean {
  return OLD_COLORS.some(color => color === node.style[prop]);
}

function processInlineTag(
  tag: string,
  node: Node,
  currentStyle: DraftInlineStyle
): DraftInlineStyle {
  var styleToCheck = inlineTags[tag];
  if (styleToCheck) {
    currentStyle = currentStyle.add(styleToCheck).toOrderedSet();
  } else if (node instanceof HTMLElement) {
    const htmlElement = node;
    currentStyle = currentStyle.withMutations(style => {
      if (htmlElement.style.fontWeight === 'bold') {
        style.add('BOLD');
      }

      if (htmlElement.style.fontStyle === 'italic') {
        style.add('ITALIC');
      }

      if (htmlElement.style.textDecoration === 'underline') {
        style.add('UNDERLINE');
      }

      if (htmlElement.style.textDecoration === 'line-through') {
        style.add('STRIKETHROUGH');
      }

      if (hasOldStyleColor(htmlElement, 'color')) {
        const styleLabel = Object.keys(OLD_INLINE_STYLES).filter(label => (
          OLD_INLINE_STYLES[label].color === htmlElement.style.color
        ))[0];
        style.add(styleLabel);
      }

      if (hasOldStyleColor(htmlElement, 'backgroundColor')) {
        const styleLabel = Object.keys(OLD_INLINE_STYLES).filter(label => (
          OLD_INLINE_STYLES[label].backgroundColor === htmlElement.style.backgroundColor
        ))[0];
        style.add(styleLabel);
      }

      if (hasOldStyleFontSize(htmlElement)) {
        const styleLabel = Object.keys(OLD_INLINE_STYLES_SIZE).filter(label => (
          OLD_INLINE_STYLES_SIZE[label].fontSize === parseInt(htmlElement.style.fontSize, 10)
        ))[0];
        style.add(styleLabel);
      }
    }).toOrderedSet();
  }
  return currentStyle;
}

function joinChunks(A: Chunk, B: Chunk): Chunk {
  // Sometimes two blocks will touch in the DOM and we need to strip the
  // extra delimiter to preserve niceness.
  var lastInB = B.text.slice(0, 1);

  if (
    A.text.slice(-1) === '\r' &&
    lastInB === '\r'
  ) {
    A.text = A.text.slice(0, -1);
    A.inlines.pop();
    A.entities.pop();
    A.blocks.pop();
  }

  // Kill whitespace after blocks
  if (
    A.text.slice(-1) === '\r'
  ) {
    if (B.text === SPACE) {
      return A;
    } else if (B.text === '\n' && A.text === '\r') {
      return B;
    } else if (lastInB === SPACE || lastInB === '\n') {
      B.text = B.text.slice(1);
      B.inlines.shift();
      B.entities.shift();
    }
  }

  return {
    text: A.text + B.text,
    inlines: A.inlines.concat(B.inlines),
    entities: A.entities.concat(B.entities),
    blocks: A.blocks.concat(B.blocks),
  };
}

/**
 * Check to see if we have anything like <p> <blockquote> <h1>... to create
 * block tags from. If we do, we can use those and ignore <div> tags. If we
 * don't, we can treat <div> tags as meaningful (unstyled) blocks.
 */
function containsSemanticBlockMarkup(html: string): boolean {
  return blockTags.some(tag => html.indexOf('<' + tag) !== -1);
}

function hasValidLinkText(link: Node): boolean {
  invariant(
    link instanceof HTMLAnchorElement,
    'Link must be an HTMLAnchorElement.'
  );
  var protocol = link.protocol;
  return protocol === 'http:' || protocol === 'https:';
}

function getAttributes(node: Node): object {
  return [].reduce.call(node.attributes, (result, { nodeName, nodeValue }) => {
    result[nodeName] = nodeValue;
    return result;
  }, {});
}

function genFragment(
  node: Node,
  inlineStyle: DraftInlineStyle,
  lastList: string,
  inBlock: ?string,
  blockTags: Array<string>,
  depth: number,
  inEntity?: string
): Chunk {
  var nodeName = node.nodeName.toLowerCase();
  var newBlock = false;
  var nextBlockType = 'unstyled';
  var lastLastBlock = lastBlock;

  // Base Case
  if (nodeName === '#text') {
    var text = node.textContent;
    if (text.trim() === '' && inBlock !== 'pre') {
      return getWhitespaceChunk(inEntity);
    }
    if (inBlock !== 'pre') {
      // Can't use empty string because MSWord
      text = text.replace(REGEX_LF, SPACE);
    }

    // save the last block so we can use it later
    lastBlock = nodeName;

    return {
      text,
      inlines: Array(text.length).fill(inlineStyle),
      entities: Array(text.length).fill(inEntity),
      blocks: [],
    };
  }

  if (Object.keys(MEDIA).some(k => k === nodeName)) {
    var entityKey = DraftEntity.create(MEDIA[nodeName], 'IMMUTABLE', {
      src: node.src,
      alt: node.alt,
      'data-original-url': node.parentNode.getAttribute('href')
    });
    return {
      text: '\r \r',
      inlines: Array(3).fill(inlineStyle),
      entities: Array(3).fill(entityKey),
      blocks: [{
        type: 'atomic',
        depth
      }, {
        type: 'unstyled',
        depth
      }]
    };
  }

  if (nodeName === 'iframe') {
    var entityKey = DraftEntity.create(IFRAME, 'IMMUTABLE', getAttributes(node));
    return {
      text: '\r \r',
      inlines: Array(3).fill(inlineStyle),
      entities: Array(3).fill(entityKey),
      blocks: [{
        type: 'atomic',
        depth
      }, {
        type: 'unstyled',
        depth
      }]
    };
  }

  // save the last block so we can use it later
  lastBlock = nodeName;

  // BR tags
  if (nodeName === 'br') {
    if (
        lastLastBlock === 'br' &&
        (!inBlock || getBlockTypeForTag(inBlock, lastList) === 'unstyled')
    ) {
      return getBlockDividerChunk('unstyled', depth);
    }
    return getSoftNewlineChunk();
  }

  var chunk = getEmptyChunk();
  var newChunk: ?Chunk = null;

  // Inline tags
  inlineStyle = processInlineTag(nodeName, node, inlineStyle);

  // Handle lists
  if (nodeName === 'ul' || nodeName === 'ol') {
    if (lastList) {
      depth += 1;
    }
    lastList = nodeName;
  }

  // Block Tags
  if (!inBlock && blockTags.indexOf(nodeName) !== -1) {
    chunk = getBlockDividerChunk(
      getBlockTypeForTag(nodeName, lastList, node),
      depth,
      node
    );
    inBlock = nodeName;
    newBlock = true;
  } else if (lastList && inBlock === 'li' && nodeName === 'li') {
    chunk = getBlockDividerChunk(
      getBlockTypeForTag(nodeName, lastList, node),
      depth,
      node
    );
    inBlock = nodeName;
    newBlock = true;
    if (lastList === 'ul') {
      if (node.classList.contains('task-list-item')) {
        nextBlockType = 'checkable-list-item';
      } else {
        nextBlockType = 'unordered-list-item';
      }
    } else {
      nextBlockType = 'ordered-list-item';
    }
  }

  // Recurse through children
  var child: ?Node = node.firstChild;
  if (child != null) {
    nodeName = child.nodeName.toLowerCase();
  }

  var entityId: ?string = null;
  var href: ?string = null;

  while (child) {
    if (nodeName === 'a' && child.href && hasValidLinkText(child)) {
      href = new URI(child.href).toString();
      if (child.hasAttribute('download')) {
        entityId = DraftEntity.create('DOWNLOAD_LINK', 'MUTABLE', {
          url: href,
          name: child.getAttribute('data-name'),
          size: child.getAttribute('data-size')
        });
      } else {
        entityId = DraftEntity.create('LINK', 'MUTABLE', { url: href });
      }
    } else {
      entityId = undefined;
    }

    newChunk = genFragment(
      child,
      inlineStyle,
      lastList,
      inBlock,
      blockTags,
      depth,
      entityId || inEntity
    );

    chunk = joinChunks(chunk, newChunk);
    var sibling: Node = child.nextSibling;

    // Put in a newline to break up blocks inside blocks
    if (
      sibling &&
      blockTags.indexOf(nodeName) >= 0 &&
      inBlock
    ) {
      chunk = joinChunks(chunk, getSoftNewlineChunk());
    }
    if (sibling) {
      nodeName = sibling.nodeName.toLowerCase();
    }
    child = sibling;
  }

  if (newBlock) {
    chunk = joinChunks(
      chunk,
      getBlockDividerChunk(nextBlockType, depth)
    );
  }

  return chunk;
}

function getChunkForHTML(html: string, DOMBuilder: Function): ?Chunk {
  html = html
    .trim()
    .replace(REGEX_CR, '')
    .replace(REGEX_NBSP, SPACE);

  var safeBody = DOMBuilder(html);
  if (!safeBody) {
    return null;
  }
  lastBlock = null;

  // Sometimes we aren't dealing with content that contains nice semantic
  // tags. In this case, use divs to separate everything out into paragraphs
  // and hope for the best.
  var workingBlocks = containsSemanticBlockMarkup(html) ? blockTags : ['div'];

  // Start with -1 block depth to offset the fact that we are passing in a fake
  // UL block to start with.
  var chunk =
    genFragment(safeBody, OrderedSet(), 'ul', null, workingBlocks, -1);

  // join with previous block to prevent weirdness on paste
  if (chunk.text.indexOf('\r') === 0) {
    chunk = {
      text: chunk.text.slice(1),
      inlines: chunk.inlines.slice(1),
      entities: chunk.entities.slice(1),
      blocks: chunk.blocks,
    };
  }

  // Kill block delimiter at the end
  if (chunk.text.slice(-1) === '\r') {
    chunk.text = chunk.text.slice(0, -1);
    chunk.inlines = chunk.inlines.slice(0, -1);
    chunk.entities = chunk.entities.slice(0, -1);
    chunk.blocks.pop();
  }

  // If we saw no block tags, put an unstyled one in
  if (chunk.blocks.length === 0) {
    chunk.blocks.push({type: 'unstyled', depth: 0});
  }

  // Sometimes we start with text that isn't in a block, which is then
  // followed by blocks. Need to fix up the blocks to add in
  // an unstyled block for this content
  if (chunk.text.split('\r').length === chunk.blocks.length + 1) {
    chunk.blocks.unshift({type: 'unstyled', depth: 0});
  }

  return chunk;
}

function convertFromHTMLtoContentBlocks(
  html: string,
  DOMBuilder: Function = getSafeBodyFromHTML,
): ?Array<ContentBlock> {
  // Be ABSOLUTELY SURE that the dom builder you pass hare won't execute
  // arbitrary code in whatever environment you're running this in. For an
  // example of how we try to do this in-browser, see getSafeBodyFromHTML.

  var chunk = getChunkForHTML(html, DOMBuilder);
  if (chunk == null) {
    return null;
  }
  var start = 0;
  return chunk.text.split('\r').map(
    (textBlock, ii) => {
      // Make absolutely certain that our text is acceptable.
      textBlock = sanitizeDraftText(textBlock);
      var end = start + textBlock.length;
      var inlines = nullthrows(chunk).inlines.slice(start, end);
      var entities = nullthrows(chunk).entities.slice(start, end);
      var characterList = List(
        inlines.map((style, ii) => {
          var data = {style, entity: (null: ?string)};
          if (entities[ii]) {
            data.entity = entities[ii];
          }
          return CharacterMetadata.create(data);
        })
      );
      start = end + 1;

      return new ContentBlock({
        key: generateRandomKey(),
        type: nullthrows(chunk).blocks[ii].type,
        depth: nullthrows(chunk).blocks[ii].depth,
        checked: nullthrows(chunk).blocks[ii].checked,
        text: textBlock,
        characterList,
      });
    }
  );
}

module.exports = convertFromHTMLtoContentBlocks;
